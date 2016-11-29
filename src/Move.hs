module Move

 where

import Control.Applicative
import Control.Arrow
--import Control.Monad.RWS hiding (msum)
import Control.Monad.Logic hiding (msum)
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Lazy
import Control.Monad.Identity hiding (msum)
--import Control.Monad
import Data.Either
import Data.List (nub, sort, intersect)
import Data.Maybe
import Data.Map hiding (map, filter, null)
import Data.Foldable (msum)

import Types
import RobotM
import Writeup


----------------------------------------------------------------------------------------------------

--renameFormula :: NextFreeIDState -> Formula -> (Formula, NextFreeIDState)



data MoveDescription = MoveDescription [StatementName] [Clause] String
data MoveType = MoveType (Tableau -> RobotM (MoveDescription, Tableau))

movetypeFromSubmovetypes :: [MoveType] -> MoveType
movetypeFromSubmovetypes ms = MoveType $ \t -> msum [f t | MoveType f <- ms]
----------------------------------------------------------------------------------------------------

type Surroundings = Tableau -> Tableau

-- tableauwise: construct a type of move that operates on each subtableau,
--   using knowledge of a) inherited hypotheses and
--                      b) the 'Surroundings', i.e. an embedding of subtableau into main tableau
tableauwise :: ([Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)) -> MoveType
tableauwise = MoveType . tableauwise'

--z :: TableauName -> TableauName
--z (TableauName n) = TableauName $ n + 100

tableauwise' :: ([Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau))
                -> Tableau
                -> RobotM (MoveDescription, Tableau)
tableauwise' f t@(Tableau tID vs hs (Target ps)) = f [] id t <|> do
    (p, context) <- oneOf $ eachElementWithContext ps
    case p of
        Left _ -> mzero
        Right t's -> do
            (t', disjunctContext) <- oneOf $ eachElementWithContext t's
            let f' :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
                f' is s = f (is ++ hs) (Tableau tID vs hs . Target . context . return . Right . disjunctContext . return . s)

            tableauwise' f' t'

tableauwise' f t@(Tableau _ _ _ Contradiction) = f [] id t
tableauwise' f t@(Done _) = f [] id t

--eltBeforeAfter  [1,2,3,4] = [(1,([],[2,3,4])),(2,([1],[3,4])),(3,([1,2],[4])),(4,([1,2,3],[]))]
eltBeforeAfter :: [a] -> [(a, ([a], [a]))]
eltBeforeAfter [] = []
eltBeforeAfter (a:as) = (a, ([], as)) : map (second (first (a:))) (eltBeforeAfter as)

--eachElementWithContext [1,2,3,4] =
--    [(1,\as->[]++as++[2,3,4]),
--     (2,\as->[1]++as++[3,4]),
--     (3,\as->[1,2]++as++[4]),
--     (4,\as->[1,2,3]++as++[])]
eachElementWithContext :: [a] -> [(a, [a] -> [a])]
eachElementWithContext = map (second glueBeforeAfter) . eltBeforeAfter where
    --glueBeforeAfter ([10,11], [20, 21]) [90, 91] = [10,11,90,91,20,21]
    glueBeforeAfter :: ([a], [a]) -> [a] -> [a]
    glueBeforeAfter (before, after) as = before ++ as ++ after

eachElementWithContextPair :: [a] -> [(a, a, [a] -> [a] -> [a])]
eachElementWithContextPair = concatMap f . eachElementWithContextPair' where
    f (a, a', context) = [(a, a', context), (a', a, flip context)]

eachElementWithContextPair' :: [a] -> [(a, a, [a] -> [a] -> [a])]
eachElementWithContextPair' as = do
    (a, (beforeA, afterA)) <- eltBeforeAfter as
    (a', (mid, afterA')) <- eltBeforeAfter afterA
    let f x y = beforeA ++ x ++ mid ++ y ++ afterA'
    return (a, a', f)

----------------------------------------------------------------------------------------------------
--
--allVariablesInFormula :: Formula -> [Variable]
--allVariablesInFormula = nub . sort . accumulateVariableInFormula return

boundVariablesInFormula :: Formula -> [Variable]
boundVariablesInFormula = nub . sort . accumulateFormula immediate where
    immediate :: Formula -> [Variable]
    immediate (AtomicFormula _ _) = []
    immediate (Not _) = []
    immediate (And _) = []
    immediate (Or _) = []
    immediate (Forall vs _) = vs
    immediate (UniversalImplies vs _ _) = vs
    immediate (Exists vs _) = vs


boundExistentialVariablesInFormula :: Formula -> [Variable]
boundExistentialVariablesInFormula = nub . sort . accumulateFormula immediate where
    immediate :: Formula -> [Variable]
    immediate (AtomicFormula _ _) = []
    immediate (Not _) = []
    immediate (And _) = []
    immediate (Or _) = []
    immediate (Forall vs _) = []
    immediate (UniversalImplies vs _ _) = []
    immediate (Exists vs _) = vs

boundUniversalVariablesInFormula :: Formula -> [Variable]
boundUniversalVariablesInFormula = nub . sort . accumulateFormula immediate where
    immediate :: Formula -> [Variable]
    immediate (AtomicFormula _ _) = []
    immediate (Not _) = []
    immediate (And _) = []
    immediate (Or _) = []
    immediate (Forall vs _) = vs
    immediate (UniversalImplies vs _ _) = vs
    immediate (Exists vs _) = []

----------------------------------------------------------------------------------------------------

hypothesesAtAnyDepth = accumulateTableau extractHypotheses where
    extractHypotheses (Tableau _ _ h's _) = h's

targetFormulaeAtAnyDepth = accumulateTableau extractTargetFormulae where
    extractTargetFormulae (Tableau _ _ _ (Target ps)) = lefts ps

----------------------------------------------------------------------------------------------------

tagAs :: Tag -> Statement -> Statement
tagAs t s@(Statement n f ts)
    | t `elem` ts = s
    | otherwise = Statement n f $ ts ++ [t]

tagStatementInTableauAs :: Tag -> StatementName -> Tableau -> Tableau
tagStatementInTableauAs tag n = mapTableau shallow where
    shallow (Tableau id vs hs (Target ps)) = Tableau id vs (onStatement <$> hs) . Target $ either (Left . onStatement) Right <$> ps
    shallow (Tableau id vs hs Contradiction) = Tableau id vs (onStatement <$> hs) Contradiction
    shallow d@(Done _) = d
    onStatement s'@(Statement n' _ _)
        | n == n' = tagAs tag s'
        | otherwise = s'


deleted :: Statement -> Bool
deleted (Statement _ _ tags) = Deleted `elem` tags

undeleted :: Statement -> Bool
undeleted = not . deleted

eachUndeletedHypothesisWithContext :: [Statement] -> [(Statement, [Statement] -> [Statement])]
eachUndeletedHypothesisWithContext = filter (undeleted . fst) . eachElementWithContext

eachUndeletedHypothesisPairWithContext :: [Statement] -> [(Statement, Statement, [Statement] -> [Statement] -> [Statement])]
eachUndeletedHypothesisPairWithContext ss = [(s, s', c) | (s, s', c) <- eachElementWithContextPair ss, undeleted s, undeleted s']

type TP = Either Statement [Tableau]

undeletedTP :: TP -> Bool
undeletedTP (Left s) = undeleted s
undeletedTP (Right _) = True

eachUndeletedTargetPartWithContext :: [TP] -> [(TP, [TP] -> [TP])]
eachUndeletedTargetPartWithContext = filter (undeletedTP . fst) . eachElementWithContext


----------------------------------------------------------------------------------------------------


addDependencies :: [Variable] -> Variable -> Variable
addDependencies vs (Variable n id t b (Dependencies ds is)) = Variable n id t b (Dependencies (map VariableTerm vs ++ ds) is)

--markDependencies:: Every time you see a \exists, That the dependency of its variable on all
--                         Previous universally quantified variables
-- e.g. Aa Eb Ac Ed P(a,b,c,d) --> Aa Eb[a] Ac Ed[a,c] P(a,b[a],c,d[a,c])
markDependencies :: Formula -> Formula
markDependencies = mapFormula shallow where
    shallow f@(AtomicFormula _ _) = f
    shallow f@(Not _) = f
    shallow f@(And fs) = f
    shallow f@(Or _) = f
    shallow (Forall vs c) = Forall vs (addD c) where
        addD = mapFormula (addDependencyToExistential vs)
    shallow (UniversalImplies vs as c) = UniversalImplies vs (map addD as) (addD c) where
        addD = mapFormula (addDependencyToExistential vs)
    shallow f@(Exists _ _) = f

    addDependencyToExistential :: [Variable] -> Formula -> Formula
    addDependencyToExistential vs f@(AtomicFormula _ _) = f
    addDependencyToExistential vs f@(Not _) = f
    addDependencyToExistential vs f@(And fs) = f
    addDependencyToExistential vs f@(Or _) = f
    addDependencyToExistential vs f@(Forall _ _) = f
    addDependencyToExistential vs f@(UniversalImplies _ _ _) = f
    addDependencyToExistential vs f@(Exists v's _) = mapVariableInFormula mark f where
        mark v
            | v `elem` v's = addDependencies vs v
            | otherwise    = v


----------------------------------------------------------------------------------------------------

isBulletedVariableChoiceLegal :: VariableChoice -> Bool
isBulletedVariableChoiceLegal (VariableChoice (Variable _ _ _ _ (Dependencies _ is)) t) =
  let ivs, dvs :: [Variable]
      ivs = nub . sort $ concatMap (accumulateVariableInTerm return) is
      dvs = accumulateVariableInTerm return t
   in null $ intersect ivs dvs  --TODO: loglinear comparison

----------------------------------------------------------------------------------------------------

-- markBulletedIndependencies vs tableau: mark every bulleted variable in tableau as being independent of vs
markBulletedIndependencies :: [Variable] -> Tableau -> Tableau
markBulletedIndependencies vs = mapVariableInTableau shallow where
    shallow (Variable n id t VTDiamond (Dependencies ds is)) = Variable n id t VTDiamond $ Dependencies ds (is ++ map VariableTerm vs)
    shallow (Variable n id t VTBullet (Dependencies ds is))  = Variable n id t VTBullet $ Dependencies ds (is ++ map VariableTerm vs)
    shallow v = v

----------------------------------------------------------------------------------------------------



conjuncts :: Formula -> [Formula]
conjuncts f@(AtomicFormula _ _) = [f]
conjuncts f@(Not _) = [f]
conjuncts f@(And fs) = concatMap conjuncts fs
conjuncts f@(Or _) = [f]
conjuncts f@(Forall _ _) = [f]
conjuncts f@(UniversalImplies _ _ _) = [f]
conjuncts f@(Exists _ f') = [f]

