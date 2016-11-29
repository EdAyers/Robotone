{-# LANGUAGE NoMonomorphismRestriction #-}

module Match (
    FormulaWithSlots(..), (/),
    Matching,
    match, matchTerm,
    emptyMatching, extendMatch,
    transform, transformTerm,
    twoWayMatchExists,
    isIsomorphic,
    matchFormulaeAmongStatements, matchFormulaeAmongFormulae,
    matchSomeOfFormulaeAmongStatements,
    extendMatchAllButOneOfFormulaeAmongStatements
) where


import Prelude hiding ((/))
import qualified Data.Map as Map
import Data.Maybe
import Data.Map (Map)
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State.Lazy

import Debug.Trace

import Types
import Move
import RobotM

----------------------------------------------------------------------------------------------------

type Matching = Map Variable Term

type MatchingM = State (Maybe Matching)
emptyMatching = Map.empty
getMatching = get
putMatching = put
modifyMatching = modify

execMatching :: Matching -> MatchingM () -> Maybe Matching
execMatching m = flip execState (Just m)

--match vs f f' : try to instantiate vs in f to make it match f'
--NB: will not match  'a and b' with 'b and a' (same for 'or', 'forall', 'exists').

match :: FormulaWithSlots -> Formula -> Maybe Matching
match = extendMatch emptyMatching

extendMatch :: Matching -> FormulaWithSlots -> Formula -> Maybe Matching
extendMatch matching (FormulaWithSlots f renamable) f' = execMatching matching $ onFormula f f' where
    onFormula :: Formula -> Formula -> MatchingM ()
    onFormula (AtomicFormula pred args) (AtomicFormula pred' args')
        | pred == pred' = zipWithM_ onTerm args args'
    onFormula (Not f) (Not f') = onFormula f f'
    onFormula (And fs) (And f's)
        | length fs == length f's = zipWithM_ onFormula fs f's
    onFormula (Or fs) (Or f's)
        | length fs == length f's = zipWithM_ onFormula fs f's
    onFormula (Forall vs f) (Forall v's f')
        | length vs == length v's  =
            sequence_ $ zipWith variableWithTerm vs (map VariableTerm v's) ++
                        [onFormula f f']
    onFormula (UniversalImplies vs ls r) (UniversalImplies v's l's r')
        | length vs == length v's && length ls == length l's =
            sequence_ $ zipWith variableWithTerm vs (map VariableTerm v's) ++
                        zipWith onFormula ls l's ++
                        [onFormula r r']
    onFormula (Exists vs f) (Exists v's f')
        | length vs == length v's  =
            sequence_ $ zipWith variableWithTerm vs (map VariableTerm v's) ++
                        [onFormula f f']
    onFormula _ _ = put Nothing

    onTerm :: Term -> Term -> MatchingM ()
    onTerm (ApplyFn fn args) (ApplyFn fn' args')
        | fn == fn' && length args == length args' = zipWithM_ onTerm args args'
    onTerm (VariableTerm v) t = variableWithTerm v t
    onTerm _ _ = put Nothing

    variableWithTerm :: Variable -> Term -> MatchingM ()
    variableWithTerm v t
        | v `elem` renamable = do
            mMatching <- getMatching
            case mMatching of
                Nothing -> return ()
                Just matching -> case Map.lookup v matching of
                    Just t' -> unless (t == t') $ put Nothing
                    Nothing -> put . Just $ Map.insert v t matching
    variableWithTerm v (VariableTerm v')
        | v == v' = return ()
    variableWithTerm _ _ = put Nothing


matchTerm :: Term -> [Variable] -> Term -> Maybe Matching
matchTerm t renamable t' = execMatching emptyMatching $ onTerm t t' where
    onTerm :: Term -> Term -> MatchingM ()
    onTerm (ApplyFn fn args) (ApplyFn fn' args')
        | fn == fn' && length args == length args' = zipWithM_ onTerm args args'
    onTerm (VariableTerm v) t = variableWithTerm v t
    onTerm _ _ = put Nothing

    variableWithTerm :: Variable -> Term -> MatchingM ()
    variableWithTerm v t
        | v `elem` renamable = do
            mMatching <- getMatching
            case mMatching of
                Nothing -> return ()
                Just matching -> case Map.lookup v matching of
                    Just t' -> unless (t == t') $ put Nothing
                    Nothing -> put . Just $ Map.insert v t matching
    variableWithTerm v (VariableTerm v')
        | v == v' = return ()
    variableWithTerm _ _ = put Nothing



transform :: Matching -> Formula -> Formula
transform = mapDirectTermInFormula . transformTerm

transformTerm :: Matching -> Term -> Term
transformTerm matching = mapTerm shallow where
    shallow :: Term -> Term
    shallow t@(VariableTerm v) = fromMaybe t (Map.lookup v matching)
    shallow t = t



----------------------------------------------------------------------------------------------------

-- Code for matching two formulas, both of which have slots. ('Two-way matching')
--this requires us to set up some machinery for unification.

--NB. Do not use this code with bulleted variables as 'slots', as it ignores all (in)dependencies.

data Equation = Term :=: Term

instance Pretty Equation where
    pretty (t :=: t') = pretty t ++ " <---> " ++ pretty t'

variableEquation :: Variable -> Variable -> Equation
variableEquation v v' = VariableTerm v :=: VariableTerm v'

--extractEquations: Match up the corresponding terms inside two formulae and
--                   return the resulting equations. If matching fails, return Nothing.
extractEquations :: Formula -> Formula -> Maybe [Equation]
extractEquations (AtomicFormula p ts) (AtomicFormula p' t's) =
    guard (p == p') >> return (zipWith (:=:) ts t's)
extractEquations (Not f) (Not f') = extractEquations f f'
extractEquations (And fs) (And f's) = do
    guard (length fs == length f's)
    concat <$> zipWithM extractEquations fs f's
extractEquations (Or fs) (Or f's) = do
    guard (length fs == length f's)
    concat <$> zipWithM extractEquations fs f's
extractEquations (Forall vs f) (Forall v's f') = do
    guard (length vs == length v's)
    innerEs <- extractEquations f f'
    return $ zipWith variableEquation vs v's ++ innerEs
extractEquations (UniversalImplies vs as c) (UniversalImplies v's a's c') = do
    guard (length vs == length v's)
    guard (length as == length a's)
    innerAntecedentEs <- concat <$> zipWithM extractEquations as a's
    innerConsequentEs <- extractEquations c c'
    return $ zipWith variableEquation vs v's ++ innerAntecedentEs ++ innerConsequentEs
extractEquations (Exists vs f) (Exists v's f') = do
    guard (length vs == length v's)
    innerEs <- extractEquations f f'
    return $ zipWith variableEquation vs v's ++ innerEs
extractEquations _ _ = Nothing


--TODO: rewrite occursIn using the Any monoid
occursIn :: Variable -> Term -> Bool
occursIn v = or . accumulateVariableInTerm (return . (== v))

--we don't want the matching algorithm to recurse into dependencies, so we will simply strip them out
removeDependencies :: Variable -> Variable
removeDependencies (Variable n id t b _) = Variable n id t b (Dependencies [] [])

removeDependenciesFromFormula :: Formula -> Formula
removeDependenciesFromFormula = mapVariableInFormula removeDependencies

--eliminate v r me = me[v := r]
eliminate :: Variable -> Term -> Equation -> Equation
eliminate v r (a :=: b) = onTerm a :=: onTerm b where
    onTerm = mapTerm shallow
    shallow (VariableTerm v')
        | v == v' = r
    shallow t = t

--twoWayMatchExists (FormulaWithSlots f vs) (FormulaWithSlots f' v's) :
--   try to instantiate vs in f and v's in f' to make them match
--NB. Assumes there is no variable collision between f and f'.
twoWayMatchExists :: FormulaWithSlots -> FormulaWithSlots -> Bool
twoWayMatchExists (FormulaWithSlots f vs) (FormulaWithSlots f' v's) =
  let renamableVs :: [Variable]
      renamableVs = removeDependencies <$> (vs ++ v's)

      renamable :: Variable -> Bool
      renamable = (`elem` renamableVs)

      --areSolvable es: is it possible to solve es by renaming vars?
      --  method: repeatedly remove a variable in all equations
      areSolvable :: [Equation] -> Bool
      areSolvable (vt@(VariableTerm v) :=: vt'@(VariableTerm v') : es)
          | v == v' = areSolvable es
          | renamable v  = areSolvable $ eliminate v  vt' <$> es
          | renamable v' = areSolvable $ eliminate v' vt  <$> es
          | otherwise = False

      areSolvable (vt@(VariableTerm v) :=: t' : es)
          | v `occursIn` t' = False   --can't match e.g. x and f(x)
          | renamable v = areSolvable $ eliminate v t' <$> es
          | otherwise = False

      areSolvable (t :=: vt'@(VariableTerm v') : es)
          | v' `occursIn` t = False   --can't match e.g. x and f(x)
          | renamable v' = areSolvable $ eliminate v' t <$> es
          | otherwise = False

      areSolvable (ApplyFn fn ts :=: ApplyFn fn' t's : es)
          | fn == fn' && length ts == length t's = areSolvable $ zipWith (:=:) ts t's ++ es
          | otherwise = False

      areSolvable [] = True

   in case extractEquations (removeDependenciesFromFormula f) (removeDependenciesFromFormula f') of
          Nothing -> False --formulae didn't match up
          Just es -> areSolvable es

--twoWayMatch (FormulaWithSlots f vs) (FormulaWithSlots f' []) = match (FormulaWithSlots f vs) f' --TODO: ***STUB***

----------------------------------------------------------------------------------------------------

isVariableTerm :: Term -> Bool
isVariableTerm (VariableTerm _) = True
isVariableTerm _ = False

isIsomorphic :: [Variable] -> Formula -> Formula -> Bool
isIsomorphic bound f f' = case match (FormulaWithSlots f bound) f' of
    Nothing -> False
    Just matching -> and [isVariableTerm t | t <- Map.elems matching]

----------------------------------------------------------------------------------------------------

--pv = parse variable
--pvs = map (parse variable) . words
--pf = parse formula
--
--a = pf "lessthan(d(x, y), delta)" / pvs "x y"
--b = pf "lessthan(d(applyfn(f,c), applyfn(f,d)), epsilon)" / pvs "epsilon"

----------------------------------------------------------------------------------------------------

--TODO: have changed all 'context []' to ss/f's. They now no longer need to be local variables of the 'go' functions.

--matchFormulaeAmongStatements vs fs ss: try to match all of fs (with vs as slots) against some of ss,
--  and if successful return match + names of ss used.
matchFormulaeAmongStatements :: [Variable] -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName])
matchFormulaeAmongStatements vs = go emptyMatching [] where

    go :: Matching -> [StatementName] -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName])
    go m ns (f:fs) ss = do
        --pick a given statement
        (Statement n f' _, context) <- oneOf $ eachElementWithContext ss

        --try to match it with the first given formula
        m' <- oneOf . maybeToList $ extendMatch m (f / boundVariablesInFormula f ++ vs) f'

        --move on to the next statement
        go m' (ns ++ [n]) fs ss

    go m ns [] _ = return (m,ns)


--matchFormulaeAmongFormulae vs fs ss: try to match all of fs (with vs as slots) against some of f's,
--  and if successful return match .
matchFormulaeAmongFormulae :: [Variable] -> [Formula] -> [Formula] -> RobotM Matching
matchFormulaeAmongFormulae vs = go emptyMatching where

    go :: Matching -> [Formula] -> [Formula] -> RobotM Matching
    go m (f:fs) f's = do
        --pick one of the f's
        (f', context) <- oneOf $ eachElementWithContext f's

        --try to match it with the first lhs formula
        m' <- oneOf . maybeToList $ extendMatch m (f / boundVariablesInFormula f ++ vs) f'

        --move on to the next statement
        go m' fs f's

    go m [] _ = return m

----matchTermsAmongTerms vs ts ss: try to match all of ts (with vs as slots) against some of t's,
----  and if successful return match .
--matchTermsAmongTerms :: [Variable] -> [Term] -> [Term] -> RobotM Matching
--matchTermsAmongTerms vs = go emptyMatching where
--
--    go :: Matching -> [Term] -> [Term] -> RobotM Matching
--    go m (t:ts) t's = do
--        --pick one of the t's
--        (t', context) <- oneOf $ eachElementWithContext t's
--
--        --try to match it with the first lhs Term
--        m' <- oneOf . maybeToList $ extendMatchTerm m (t / boundVariablesInFormula t ++ vs) t'
--
--        --move on to the next statement
--        go m' ts (context [])
--
--    go m [] _ = return m


extendMatchAllButOneOfFormulaeAmongStatements :: Matching -> [Variable] -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName], Formula)
extendMatchAllButOneOfFormulaeAmongStatements m vs = go m [] Nothing where

    go :: Matching -> [StatementName] -> Maybe Formula -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName], Formula)
    go m ns Nothing [] _ = error "matchAllButOneOfFormulaeAmongStatements called with no formulae."
    go m ns Nothing [f] _ = return (m,ns,f)
    go m ns mLeftoverF (f:fs) ss = do
        --pick a given statement
        (Statement n f' _, context) <- oneOf $ eachElementWithContext ss

        --try to match it with the first given formula
        case extendMatch m (f / boundVariablesInFormula f ++ vs) f' of
            Just m' -> go m' (ns ++ [n]) mLeftoverF fs ss --keep going
            Nothing -> case mLeftoverF of
                Just _ -> mzero  --two leftover formulae
                Nothing -> go m ns (Just f) fs ss --first unmatchable formula found

    go m ns (Just l) [] _ = return (m,ns,l)


matchSomeOfFormulaeAmongStatements :: [Variable] -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName], [Formula])
matchSomeOfFormulaeAmongStatements = extendMatchSomeOfFormulaeAmongStatements emptyMatching

extendMatchSomeOfFormulaeAmongStatements :: Matching -> [Variable] -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName], [Formula])
extendMatchSomeOfFormulaeAmongStatements m vs = go m [] [] where

    go :: Matching -> [StatementName] -> [Formula] -> [Formula] -> [Statement] -> RobotM (Matching, [StatementName], [Formula])
    go m ns leftovers (f:fs) ss = do
        --pick a given statement
        (Statement n f' _, context) <- oneOf $ eachElementWithContext ss

        --try to match it with the first given formula
        case extendMatch m (f / boundVariablesInFormula f ++ vs) f' of
            Just m' -> go m' (ns ++ [n]) leftovers fs ss --keep going
            Nothing ->  go m ns (leftovers ++ [f]) fs ss --first unmatchable formula found

    go m ns leftovers [] _ = return (m,ns,leftovers)
