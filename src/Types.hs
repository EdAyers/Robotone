{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Types where


import Prelude hiding (repeat, (/))
import Control.Applicative
import Data.Functor.Identity
import Control.Monad
import Control.Monad.Writer.Lazy (Writer, tell, runWriter)
import Data.Monoid
import Data.List
import Debug.Trace

import TexBase

----------------------------------------------------------------------------------------------------

data Function = Function String                                             deriving (Eq, Ord, Show)
data Predicate = Predicate String                                           deriving (Eq, Ord, Show)

type ID = Int
type HasBullet = Bool  --TODO: rename to isKey/hasDagger

data Type_ = TPoint | TSet | TFunction | TPositiveRealNumber | TSequence | TNaturalNumber | TGroup
                                                                            deriving (Eq, Ord, Show)
data VariableType = VTNormal | VTDiamond | VTBullet                         deriving (Eq, Ord, Show)

--TODO: Independencies should be variables, not terms.
data Dependencies = Dependencies [Term] {-dep-} [Term] {-indep-}            deriving (Eq, Ord, Show)

data Variable = Variable String ID Type_ VariableType Dependencies          deriving (Eq, Ord, Show)

data Term = VariableTerm Variable
          | ApplyFn Function [Term]                                         deriving (Eq, Ord, Show)

data Formula = AtomicFormula Predicate [Term]
             | Not Formula
             | And [Formula]
             | Or [Formula]
             | Forall [Variable] Formula
             | UniversalImplies [Variable] [Formula] Formula
             | Exists [Variable] Formula                                    deriving (Eq, Ord, Show)


data FormulaWithSlots = FormulaWithSlots Formula [Variable]                 deriving (Eq, Ord, Show)
(/) :: Formula -> [Variable] -> FormulaWithSlots
(/) = FormulaWithSlots

infixr 4 /

data StatementType = STHypothesis | STTarget                                deriving (Eq, Ord, Show)

data StatementName = StatementName StatementType ID                         deriving (Eq, Ord, Show)

data Tag = Vulnerable
         | Deleted
         | MovedDownFrom TableauName
         | UsedForwardsWith  [StatementName]
         | UsedBackwardsWith [StatementName]
         | CannotSubstitute [[Term]]                                        deriving (Eq, Ord, Show)


data Statement = Statement StatementName Formula [Tag]                      deriving (Eq, Ord, Show)

type IsUnlocked = Bool

data TableauName = TableauName IsUnlocked ID                                deriving (Eq, Ord, Show)

data Tableau = Tableau TableauName [Variable] [Statement] Target
             | Done TableauName                                             deriving (Eq, Ord, Show)

data Target = Target [Either Statement [Tableau]] --tableaux are disjunctive
            | Contradiction                                                 deriving (Eq, Ord, Show)

data VariableChoice = VariableChoice Variable Term                          deriving (Eq, Ord, Show)

data Problem = Problem String [String] String                               deriving (Eq, Ord, Show)

----------------------------------------------------------------------------------------------------
prettyID :: ID -> String
prettyID n = replicate (n-1) '\''

prettyVariableNameID :: String -> ID -> String
prettyVariableNameID s id = s ++ prettyID id

class Pretty a where
    pretty :: a -> String

instance Pretty Function where
    pretty (Function s) = s
instance Pretty Predicate where
    pretty (Predicate s) = s

instance Pretty Dependencies where
    pretty (Dependencies [] []) = ""
    pretty (Dependencies ds is) = "[" ++ intercalate "," (map pretty ds ++ (("-"++). pretty <$> is)) ++ "]"

instance Pretty VariableType where
    pretty VTNormal = ""
    pretty VTDiamond = "D"
    pretty VTBullet = "B"

instance Pretty Variable where
    pretty (Variable s id _ vtype d) =
        prettyVariableNameID s id ++ pretty vtype ++ pretty d


instance Pretty Term where
    pretty (ApplyFn (Function "intersect") [a,b]) = pretty a ++ " cap " ++ pretty b

    pretty (VariableTerm v) = pretty v
    pretty (ApplyFn fn args) = pretty fn ++ "(" ++ intercalate "," (pretty <$> args) ++ ")"

instance Pretty Formula where
    pretty (AtomicFormula (Predicate "in") [a,b]) = pretty a ++ " in " ++ pretty b
    pretty (AtomicFormula (Predicate "lessthan") [a,b]) = pretty a ++ "<" ++ pretty b
    pretty (AtomicFormula (Predicate "open") [a]) = pretty a ++ " is open"

    pretty (AtomicFormula pred args) = pretty pred ++ "(" ++ intercalate "," (pretty <$> args) ++ ")"
    pretty (Not f) = "¬" ++ pretty f
    pretty (And fs) = intercalate " & " $ pretty <$> fs
    pretty (Or fs) = intercalate " v " $ pretty <$> fs
    pretty (Forall vs f) = "forall " ++ intercalate ", " (pretty <$> vs) ++ ".(" ++ pretty f ++ ")"
    pretty (UniversalImplies vs fs f') = "forall " ++ intercalate ", " (pretty <$> vs) ++
                                           ".(" ++ pretty (And fs) ++ " => " ++ pretty f' ++ ")"
    pretty (Exists vs f) = "exists " ++ intercalate ", " (pretty <$> vs) ++ ".(" ++ pretty f ++ ")"

instance Pretty FormulaWithSlots where
    pretty (FormulaWithSlots f vs) = "(" ++ pretty f ++ "/" ++ unwords (pretty <$> vs) ++ ")"

instance Pretty StatementType where
    pretty STHypothesis = "H"
    pretty STTarget = "T"

instance Pretty StatementName where
    pretty (StatementName t id) = pretty t ++ show id

instance Pretty Statement where
    pretty (Statement n f _) = pretty n ++ ". " ++ pretty f

instance Pretty Tableau where
    pretty (Tableau id vs ss t) = unlines $
        [show id] ++
        (pretty <$> ss) ++
        ["--------",
        pretty t]
    pretty (Done _) = "Done"

instance Pretty Target where  --output goes inside an array env.
    pretty (Target ps) = unlines [either pretty (unlines . map pretty) p | p <- ps]
    pretty Contradiction = "Contradiction"

----------------------------------------------------------------------------------------------------

allVariablesInTerm :: Term -> [Variable]
allVariablesInTerm = nub . sort . accumulateVariableInTerm return

allVariablesInFormula :: Formula -> [Variable]
allVariablesInFormula = nub . sort . accumulateVariableInFormula return



allDirectVariablesInFormula :: Formula -> [Variable]
allDirectVariablesInFormula = nub . sort . accumulateDirectVariableInFormula return
----------------------------------------------------------------------------------------------------

--mapXM: drills down through X to find all subXs
--mapDirectXInYM: drills down through Ys to find Xs; does not look inside Xs
--mapDirectXInYM: drills down through Ys to find Xs; does look inside Xs


mapVariableM :: Monad m => (Variable -> m Variable) -> Variable -> m Variable
mapVariableM fn (Variable n id t bs (Dependencies ds is)) =
    fn =<< Variable n id t bs `liftM` (return Dependencies `ap` mapM (mapDirectVariableInTermM $ mapVariableM fn) ds
                                                           `ap` mapM (mapDirectVariableInTermM $ mapVariableM fn) is)

mapDirectTermInVariableM :: Monad m => (Term -> m Term) -> Variable -> m Variable
mapDirectTermInVariableM fn (Variable n id t bs (Dependencies ds is)) =
    Variable n id t bs `liftM` (return Dependencies `ap` mapM fn ds `ap` mapM fn is)

mapTermInVariableM = mapDirectTermInVariableM . mapTermM

mapTermM :: Monad m => (Term -> m Term) -> Term -> m Term
mapTermM f (VariableTerm (Variable n id t bs (Dependencies ds is))) =
    f . VariableTerm . Variable n id t bs =<< return Dependencies `ap` mapM (mapTermM f) ds
                                                                  `ap` mapM (mapTermM f) is
mapTermM f (ApplyFn fn args) = f . ApplyFn fn =<< mapM (mapTermM f) args

mapDirectVariableInTermM :: Monad m => (Variable -> m Variable) -> Term -> m Term
mapDirectVariableInTermM f (VariableTerm v) = VariableTerm `liftM` f v
mapDirectVariableInTermM f (ApplyFn fn args) = ApplyFn fn `liftM` mapM (mapDirectVariableInTermM f) args

mapVariableInTermM = mapDirectVariableInTermM . mapVariableM


mapFormulaM :: Monad m => (Formula -> m Formula) -> Formula -> m Formula
mapFormulaM fn f@(AtomicFormula _ _) = fn f
mapFormulaM fn (Not f) = fn . Not =<< mapFormulaM fn f
mapFormulaM fn (And fs) = fn . And =<< mapM (mapFormulaM fn) fs
mapFormulaM fn (Or fs) = fn . Or =<< mapM (mapFormulaM fn) fs
mapFormulaM fn (Forall vs f) = fn . Forall vs =<< mapFormulaM fn f
mapFormulaM fn (UniversalImplies vs fs f') = fn =<< UniversalImplies vs `liftM` mapM (mapFormulaM fn) fs `ap` mapFormulaM fn f'
mapFormulaM fn (Exists vs f) = fn . Exists vs =<< mapFormulaM fn f

mapDirectVariableInFormulaM :: Monad m => (Variable -> m Variable) -> Formula -> m Formula
mapDirectVariableInFormulaM  fn = mapFormulaM immediate where
    immediate (AtomicFormula pred args) = AtomicFormula pred `liftM` mapM (mapDirectVariableInTermM fn) args
    immediate f@(Not _) = return f
    immediate f@(And _) = return f
    immediate f@(Or _) = return f
    immediate (Forall vs f) =              Forall           `liftM` mapM fn vs `ap` return f
    immediate (UniversalImplies vs as c) = UniversalImplies `liftM` mapM fn vs `ap` return as `ap` return c
    immediate (Exists vs f) =              Exists           `liftM` mapM fn vs `ap` return f

mapVariableInFormulaM = mapDirectVariableInFormulaM . mapVariableM

--mapDirectTermInFormulaM: drills down through formulae to find terms; does not look inside terms
mapDirectTermInFormulaM :: Monad m => (Term -> m Term) -> Formula -> m Formula
mapDirectTermInFormulaM fn = mapFormulaM onDirectSubterm where
    onDirectSubterm (AtomicFormula pred args) = AtomicFormula pred `liftM` mapM fn args
    onDirectSubterm f@(Not _) = return f
    onDirectSubterm f@(And _) = return f
    onDirectSubterm f@(Or _) = return f
    onDirectSubterm (Forall vs f) = Forall `liftM` mapM (mapDirectTermInVariableM fn) vs `ap` return f
    onDirectSubterm (UniversalImplies vs as c) = UniversalImplies `liftM` mapM (mapDirectTermInVariableM fn) vs `ap` return as `ap` return c
    onDirectSubterm (Exists vs f) = Exists `liftM` mapM (mapDirectTermInVariableM fn) vs `ap` return f

mapTermInFormulaM :: Monad m => (Term -> m Term) -> Formula -> m Formula --deep (affects all subterms)
mapTermInFormulaM = mapDirectTermInFormulaM . mapTermM

mapDirectFormulaInStatementM :: Monad m => (Formula -> m Formula) -> Statement -> m Statement
mapDirectFormulaInStatementM fn (Statement n f ts) = return (Statement n) `ap` fn f `ap` return ts


eitherM :: Monad m => (a -> m a) -> (b -> m b) -> Either a b -> m (Either a b)
eitherM f g = either (liftM Left . f) (liftM Right . g)

--mapTableauM : deep (affacts all subtableau of given tableau)
mapTableauM :: forall m. Monad m => (Tableau -> m Tableau) -> Tableau -> m Tableau
mapTableauM fn (Tableau id vs hs t) = fn =<< Tableau id vs hs `liftM` inTargetM t where
    inTargetM :: Target -> m Target
    inTargetM (Target ps) = Target `liftM` mapM g ps where
        g :: Either Statement [Tableau] -> m (Either Statement [Tableau])
        g = eitherM return $ mapM (mapTableauM fn)
    inTargetM Contradiction = return Contradiction
mapTableauM fn d@(Done _) = fn d

--TODO: tidy this next function
mapDirectVariableInTableauM :: forall m. Monad m => (Variable -> m Variable) -> Tableau -> m Tableau
mapDirectVariableInTableauM fn (Tableau id vs hs t) =
        return (Tableau id) `ap` mapM fn vs
                            `ap` mapM (mapDirectFormulaInStatementM $ mapDirectVariableInFormulaM fn) hs
                            `ap` inTargetM t where
    inTargetM :: Target -> m Target
    inTargetM (Target ps) = liftM Target (mapM g ps) where
        g :: Either Statement [Tableau] -> m (Either Statement [Tableau])
        g = eitherM (mapDirectFormulaInStatementM $ mapDirectVariableInFormulaM fn)
                    (mapM (mapDirectVariableInTableauM fn))
    inTargetM Contradiction = return Contradiction
mapDirectVariableInTableauM _ d@(Done _) = return d

mapVariableInTableauM = mapDirectVariableInTableauM . mapVariableM

mapDirectTermInTableauM :: Monad m => (Term-> m Term) -> Tableau -> m Tableau --deep (affects all terms)
mapDirectTermInTableauM = mapDirectFormulaInTableauM . mapDirectTermInFormulaM

mapTermInTableauM :: Monad m => (Term-> m Term) -> Tableau -> m Tableau --deep (affects all terms)
mapTermInTableauM = mapDirectFormulaInTableauM . mapTermInFormulaM

--mapDirectFormulaInTableauM: drills down through tableaux and targets to find formulae; does not look inside formulae
mapDirectFormulaInTableauM :: forall m. Monad m => (Formula -> m Formula) -> Tableau -> m Tableau
mapDirectFormulaInTableauM fn (Tableau id vs hs t) = return (Tableau id vs) `ap` mapM (mapDirectFormulaInStatementM fn) hs
                                                                            `ap` inTargetM t where
    inTargetM :: Target -> m Target
    inTargetM (Target ps) = Target `liftM` mapM g ps where
        g :: Either Statement [Tableau] -> m (Either Statement [Tableau])
        g = eitherM (mapDirectFormulaInStatementM fn)
                    (mapM $ mapDirectFormulaInTableauM fn)
    inTargetM Contradiction = return Contradiction
mapDirectFormulaInTableauM _ d@(Done _) = return d

mapFormulaInTableauM :: Monad m => (Formula -> m Formula) -> Tableau -> m Tableau --deep (affects all subformulae)
mapFormulaInTableauM = mapDirectFormulaInTableauM . mapFormulaM

----------------------------------------------------------------------------------------------------

nonmonadic :: ((a -> Identity a) -> b-> Identity b) -> (a -> a) -> b -> b
nonmonadic mm f = runIdentity . mm (return . f)

mapVariable = nonmonadic mapVariableM
mapTerm = nonmonadic mapTermM
mapTermInVariable = nonmonadic mapTermInVariableM
mapDirectVariableInTerm = nonmonadic mapDirectVariableInTermM
mapVariableInTerm = nonmonadic mapVariableInTermM

mapFormula = nonmonadic mapFormulaM
mapDirectVariableInFormula = nonmonadic mapDirectVariableInFormulaM
mapVariableInFormula = nonmonadic mapVariableInFormulaM
mapDirectTermInFormula = nonmonadic mapDirectTermInFormulaM
mapTermInFormula = nonmonadic mapTermInFormulaM

mapTableau = nonmonadic mapTableauM
mapDirectVariableInTableau = nonmonadic mapDirectVariableInTableauM
mapVariableInTableau = nonmonadic mapVariableInTableauM
mapDirectTermInTableau = nonmonadic mapDirectTermInTableauM
mapTermInTableau = nonmonadic mapTermInTableauM
mapDirectFormulaInTableau = nonmonadic mapDirectFormulaInTableauM
mapFormulaInTableau = nonmonadic mapFormulaInTableauM

----------------------------------------------------------------------------------------------------

accumulate :: forall w. forall a. forall b. (Monoid w) => ((a -> Writer w a) -> b-> Writer w b) -> (a -> w) -> b -> w
accumulate mm f = snd . runWriter . mm write
  where write :: a -> Writer w a
        write = liftM2 (>>) (tell . f) return

accumulateVariable = accumulate mapVariableM
accumulateTerm = accumulate mapTermM
accumulateTermInVariable = accumulate mapTermInVariableM
accumulateDirectVariableInTerm = accumulate mapDirectVariableInTermM
accumulateVariableInTerm = accumulate mapVariableInTermM

accumulateFormula = accumulate mapFormulaM
accumulateDirectVariableInFormula = accumulate mapDirectVariableInFormulaM
accumulateVariableInFormula = accumulate mapVariableInFormulaM
accumulateDirectTermInFormula = accumulate mapDirectTermInFormulaM
accumulateTermInFormula = accumulate mapTermInFormulaM

accumulateTableau :: Monoid w => (Tableau -> w) -> Tableau -> w
accumulateTableau = accumulate mapTableauM
accumulateDirectVariableInTableau = accumulate mapDirectVariableInTableauM
accumulateVariableInTableau = accumulate mapVariableInTableauM
accumulateDirectTermInTableau = accumulate mapDirectTermInTableauM
accumulateTermInTableau = accumulate mapTermInTableauM
accumulateDirectFormulaInTableau = accumulate mapDirectFormulaInTableauM
accumulateFormulaInTableau = accumulate mapFormulaInTableauM

----------------------------------------------------------------------------------------------------

isAtomic :: Formula -> Bool
isAtomic (AtomicFormula _ _) = True
isAtomic (Not _) = True
isAtomic (And fs) = True
isAtomic (Or _) = True
isAtomic (Forall _ _) = False
isAtomic (UniversalImplies _ _ _) = False
isAtomic (Exists _ _) = False

isBulletedOrDiamonded :: Variable -> Bool
isBulletedOrDiamonded (Variable _ _ _ VTNormal _) = False
isBulletedOrDiamonded (Variable _ _ _ VTDiamond _) = True
isBulletedOrDiamonded (Variable _ _ _ VTBullet _) = True

----------------------------------------------------------------------------------------------------
