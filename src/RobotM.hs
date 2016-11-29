module RobotM (
    oneOf,
    RobotM(..),
    askPrintingData,
    askLibrary,
    askLibraryResult, askLibrarySolution, askLibraryExpansionTable, askLibraryRewriteTable,
    RobotState(..), initialRobotState, getRobotState, putRobotState,
    runRobotM, runAllRobotM, evalAllRobotM,
    speculative,
    renameFormula,
    createStatement, createTableau, createTableau',
    copyStatement, copyTableau, copyTarget
) where

import Control.Applicative
import Control.Arrow
import Control.Monad.Logic hiding (msum)
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Reader
import Control.Monad.Identity hiding (msum)
import Data.Either
import Data.List (nub, sort)
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map, (!), member, notMember)
import Data.Foldable (msum)


import Types
import Library
import Printing

----------------------------------------------------------------------------------------------------

-- in a do-block in the [] monad, one can write
--    x <- [a,b,c]
-- in a more general nondeterministic monad (made with LogicT M),
--  one wants to be able to write something similar, as in
--    x <- oneOf [a,b,c]

oneOf :: MonadPlus m => [a] -> m a
oneOf = msum . map return

----------------------------------------------------------------------------------------------------

type VarNameCount = Map String Int

type NextTableauID = Int
initialNextTableauID = 1
type NextStatementIDs = Map StatementType Int
initialNextStatementIDs = Map.empty

data RobotState = RobotState NextTableauID NextStatementIDs VarNameCount
initialRobotState = RobotState initialNextTableauID initialNextStatementIDs Map.empty

type RobotM = StateT RobotState (LogicT (ReaderT (PrintingData, Library) Identity))

runRobotM :: PrintingData -> Library -> RobotState -> RobotM a -> Maybe (a, RobotState)
runRobotM p l s ma = listToMaybe . runIdentity . flip runReaderT (p,l) . observeManyT 1 $ runStateT ma s

runAllRobotM :: PrintingData -> Library -> RobotState -> RobotM a -> [(a, RobotState)]
runAllRobotM p l s ma = runIdentity . flip runReaderT (p,l) . observeAllT $ runStateT ma s

evalAllRobotM :: PrintingData -> Library -> RobotState -> RobotM a -> [a]
evalAllRobotM p l s = map fst . runAllRobotM p l s

getRobotState :: RobotM RobotState
getRobotState = get

putRobotState :: RobotState -> RobotM ()
putRobotState = put


askPrintingData :: RobotM PrintingData
askPrintingData = fst `liftM` (lift $ lift ask)

askLibrary :: RobotM Library
askLibrary = snd `liftM` (lift $ lift ask)

askLibraryResult :: RobotM Result
askLibraryResult = do
    Library rs _ _ _ <- askLibrary
    r <- oneOf rs
    renameResult r --variables bound by explicit quantifiers inside results need to be rebound
                   -- (and renaming implicitly bound variables is harmless)

--NB: Solutions are not renamed as they should not contain bound variables.
askLibrarySolution :: RobotM Solution
askLibrarySolution = do
    Library _ ss _ _ <- askLibrary
    oneOf ss

askLibraryExpansionTable :: RobotM ExpansionTable
askLibraryExpansionTable = do
    Library _ _ et _ <- askLibrary
    return et

askLibraryRewriteTable :: RobotM RewriteTable
askLibraryRewriteTable = do
    Library _ _ _ rt <- askLibrary
    return rt


--speculative ma: Find out what the effect of running ma would be, but don't modify the state.
--Typically used when we want to rename but not claim variables from the stock.

--  NB: if you have a renamed formula produced in this way, DO NOT use it with
--        any other expanded statement, as this may cause variable collision.
--  In such cases (speculative expansion of many formulae), use getRobotState/putRobotState

speculative :: RobotM a -> RobotM a
speculative ma = do
    s <- get
    a <- ma
    put s
    return a

--VarNameCount functions:
getVarNameCount :: RobotM VarNameCount
getVarNameCount = do
    RobotState _ _ v <- get
    return v

putVarNameCount :: VarNameCount -> RobotM ()
putVarNameCount v = do
    RobotState t s _ <- get
    put $ RobotState t s v

--Sometimes variables can be given in the problem, rather than produced by renaming.
--When we see such variables we need to update the VarNameCount
--   to make sure we don't generate Variables with the same names when renaming.
registerVariables :: [Variable] -> RobotM ()
registerVariables vs = do
    vnc <- getVarNameCount
    putVarNameCount $ foldr register vnc [(n, id) | Variable n id _ _ _ <- vs]

register :: (String, ID) -> VarNameCount -> VarNameCount
register (n,id) = Map.insertWith max n (id + 1)

----------------------------------------------------------------------------------------------------

-- RenameM renumbers *bound* variables in any number of formulae (e.g. from the Library),
--  avoiding numbers that are already used (and updating the underlying RobotM)
-- Note that each time we pull a fresh formula out of a library, we need a new RenameM
--  so that any "colliding" variables used in different formulae are renamed to different things.
-- Conversely if (for whatever reason) we want to rename two formulae in a consistent manner,
--  we must use one RenameM.

boundNamesInFormula :: Formula -> [(String, ID)]
boundNamesInFormula = accumulateFormula immediate where
    immediate :: Formula -> [(String, ID)]
    immediate (AtomicFormula _ _) = []
    immediate (Not _) = []
    immediate (And _) = []
    immediate (Or _) = []
    immediate (Forall vs _) = [(n,id) | Variable n id _ _ _ <- vs]
    immediate (UniversalImplies vs _ _) = [(n,id) | Variable n id _ _ _ <- vs]
    immediate (Exists vs _) = [(n,id) | Variable n id _ _ _ <- vs]

type VarNameMap = Map (String, ID) (String, ID)
type RenameM = StateT VarNameMap RobotM

getVarNameMap :: RenameM VarNameMap
getVarNameMap  = get

putVarNameMap :: VarNameMap -> RenameM ()
putVarNameMap  = put

modifyVarNameMap  = modify

getVarNameCount' = lift getVarNameCount
putVarNameCount' = lift . putVarNameCount

renameNameid :: [(String, ID)] -> (String, ID)  -> Type_ -> RenameM (String, ID)
renameNameid bounds n' t
    | n' `elem` bounds = maybe (renameUnfamiliarNameid n' t) return
                          . Map.lookup n'
                          =<< getVarNameMap
    | otherwise = return n' --don't rename free variables

renameUnfamiliarNameid :: (String, ID)  -> Type_ -> RenameM (String, ID)
renameUnfamiliarNameid n@(name, _) t = do
    nc <- getVarNameCount' :: RenameM (Map String Int)
    let unusedNames = filter (`notMember` nc) $ name:fallbacks t
        n'@(name', id') =
            head $ [(u,1) | u <- unusedNames] ++   --take an unused name if possible,
                   [(name, nc!name)]               -- else add primes to original name
    modifyVarNameMap $ Map.insert n n'
    putVarNameCount' $ Map.insert name' (id'+1) nc
    return n'

fallbacks :: Type_ -> [String]
fallbacks TPositiveRealNumber = ["eta", "theta", "alpha", "beta", "gamma"]
fallbacks TPoint = ["z", "u", "v", "w", "p", "q", "r", "s", "t"]
fallbacks _ = []



renameFormula' :: Formula -> RenameM Formula
renameFormula' f = mapFormulaM shallow f where
    bounds = boundNamesInFormula f

    shallow :: Formula -> RenameM Formula
    shallow (AtomicFormula pred args) = AtomicFormula pred <$> mapM (mapTermM onTermShallow) args
    shallow f@(Not _) = return f
    shallow f@(And _) = return f
    shallow f@(Or _) = return f
    shallow (Forall vs f's) = liftM2 Forall (mapM onVariable vs) (return f's)
    shallow (UniversalImplies vs f's f'') = liftM3 UniversalImplies (mapM onVariable vs) (return f's) (return f'')
    shallow (Exists vs f's) = liftM2 Exists (mapM onVariable vs) (return f's)

    onTermShallow :: Term -> RenameM Term
    onTermShallow (VariableTerm var) = VariableTerm <$> onVariable var
    onTermShallow t = return t

    onVariable :: Variable -> RenameM Variable
    onVariable = mapVariableM onVariableShallow

    onVariableShallow :: Variable -> RenameM Variable
    onVariableShallow (Variable name id t hasBullet dependencies) = do
        (name', id') <- renameNameid bounds (name, id) t
        return $ Variable name' id' t hasBullet dependencies

renameFormula :: Formula -> RobotM Formula
renameFormula f = evalStateT (renameFormula' f) Map.empty

renameResult' :: Result -> RenameM Result
renameResult' (Result d ps c) = do
    ps' <- mapM renameFormula' ps
    c' <- renameFormula' c
    return $ Result d ps' c'

renameResult :: Result -> RobotM Result
renameResult f = evalStateT (renameResult' f) Map.empty


----------------------------------------------------------------------------------------------------
--All of the following functions are in the RobotM monad
--  because they need to uniquely number Statements or Tableaux
--Some also affect variables (see below).

getNewTableauID :: RobotM ID
getNewTableauID = do
    RobotState t s v <- get
    put $ RobotState (t+1) s v
    return t

getNewStatementID :: StatementType -> RobotM ID
getNewStatementID t = do
    RobotState tab s v <- get
    let n = Map.findWithDefault 1 t s
    put $ RobotState tab (Map.insert t (n+1) s) v
    return n

--createStatement, createTableau do not rename any variables in the formulae they are given,
--  but they do register the names of these variables (to avoid collision during renaming)
createStatement :: StatementType -> Formula -> RobotM Statement
createStatement t f = do
    let vs = accumulateVariableInFormula return f
    registerVariables vs
    id <- getNewStatementID t
    return $ Statement (StatementName t id) f []

createTableau :: Bool -> [Formula] -> Formula -> RobotM Tableau
createTableau d hs t = do
    id' <- getNewTableauID
    hs' <- mapM (createStatement STHypothesis) hs
    t' <- createStatement STTarget t
    return $ Tableau (TableauName d id') [] hs' (Target [Left t'])


createTableau' :: Bool -> [Statement] -> Target -> RobotM Tableau
createTableau' d hs t = do
    id' <- getNewTableauID
    return $ Tableau (TableauName d id') [] hs t

--copyStatement, copyTableau, copyTarget rename bound variables in their arguments.

copyStatement :: Statement -> RobotM Statement
copyStatement (Statement (StatementName t _) f tags) = do
    id <- getNewStatementID t
    f' <- renameFormula f
    return $ Statement (StatementName t id) f' tags

copyTableau :: Tableau -> RobotM Tableau
copyTableau (Tableau (TableauName d _) vs hs t) = liftM4 Tableau (TableauName d `liftM ` getNewTableauID)
                                                 (return vs)
                                                 (mapM copyStatement hs)
                                                 (copyTarget t)

copyTarget :: Target -> RobotM Target
copyTarget (Target ps) = Target <$> mapM onPart ps where
    onPart = eitherM copyStatement (mapM copyTableau)

--eitherM :: Monad m => (a -> m a) -> (b -> m b) -> Either a b -> m (Either a b)
--eitherM f g = either (liftM Left . f) (liftM Right . g)

----------------------------------------------------------------------------------------------------

