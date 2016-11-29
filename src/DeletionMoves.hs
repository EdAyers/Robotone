module DeletionMoves (
    deleteDone,
    deleteDoneDisjunct,
    deleteRedundantHypothesis,
    deleteDangling,
    deleteUnmatchable
) where

import Prelude hiding ((/))
import Control.Arrow
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Map as Map
import Data.Map (Map, (!))

import Types
import Move
import Match
import Expansion
import TexBase
import Tex
import RobotM

import Debug.Trace

----------------------------------------------------------------------------------------------------

boundVars =  boundVariablesInFormula

----------------------------------------------------------------------------------------------------

replaceTargetStatementWithTableau :: StatementName -> Tableau -> Tableau -> Tableau
replaceTargetStatementWithTableau n rep = mapTableau shallow where
    shallow tableau@(Tableau tID tVs hs t@(Target ps)) =
        case [c | (Left t@(Statement n' _ _), c) <- eachUndeletedTargetPartWithContext ps, n == n'] of
            [context] -> Tableau tID tVs hs . Target $ context [Right [rep]]
            [] -> tableau
    shallow tableau = tableau

----------------------------------------------------------------------------------------------------

--TODO: check whether these fns are exhaustive, i.e. kill all possible 'Done' configurations

isDone :: Tableau -> Bool
isDone (Done _) = True
isDone _ = False
--
--isSingleDone :: [Tableau] -> Bool
--isSingleDone [Done _] = True
--isSingleDone _ = False

isSingleDoneTP :: Either Statement [Tableau] -> Bool
isSingleDoneTP (Right [Done _]) = True
isSingleDoneTP _ = False

deleteDone :: MoveType
deleteDone = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do
        guard $ any isSingleDoneTP ps --some target part consists of a single 'Done'

        let notDone = filter (not . isSingleDoneTP) ps

        case notDone of
            [] -> return (MoveDescription [] [] $
                    "All targets of " ++ texTN tID ++ " are `Done', so " ++ texTN tID ++ " is itself done.",
                s $ Done tID)

            ps -> return (MoveDescription [] [] $
                    "Remove `Done' targets of " ++ texTN tID ++ ".",
                s . Tableau tID tVs hs . Target $ ps)

    onTableau _ _ _ = mzero

deleteDoneDisjunct :: MoveType
deleteDoneDisjunct = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do

        (Right ts, targetContext) <- oneOf $ eachUndeletedTargetPartWithContext ps

        guard $ any isDone ts --some disjunct tableau is 'Done'

        case targetContext [] of
            [] -> return (MoveDescription [] [] $
                    "Some disjunct of the target of " ++ texTN tID ++ " is `Done', so " ++ texTN tID ++ " is itself `Done'.",
                s $ Done tID)

            ps -> return (MoveDescription [] [] $
                    "Some disjunct of a target line of " ++ texTN tID ++ " is `Done', so we will remove the line.",
                s . Tableau tID tVs hs . Target $ ps)


    onTableau _ _ _ = mzero


----------------------------------------------------------------------------------------------------

deleteRedundantHypothesis :: MoveType
deleteRedundantHypothesis = movetypeFromSubmovetypes [
    tagRedundantForwardsImplication,
    tagRedundantBackwardsImplication
  --TODO: add the submoves relating to conjunctions and disjunctions
  ]


--removeExistentialQuantifiers:
removeExistentialQuantifiers :: Formula -> Formula
removeExistentialQuantifiers f@(AtomicFormula _ _) = f
removeExistentialQuantifiers f@(Not _) = f
removeExistentialQuantifiers f@(And _) = f
removeExistentialQuantifiers f@(Or _) = f
removeExistentialQuantifiers f@(Forall _ _) = f
removeExistentialQuantifiers f@(UniversalImplies _ _ _) = f
removeExistentialQuantifiers f@(Exists vs f') = removeExistentialQuantifiers f'

tagRedundantForwardsImplication :: MoveType
tagRedundantForwardsImplication = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t) = do
        -- Find a one-variable implicative hypothesis (possibly using expansion)
        (Statement n f tags, context) <- oneOf $ eachElementWithContext hs
        UniversalImplies vs [_] consequent <- return f <|> speculative (primaryExpansion f)
        let otherHs = context []

        -- Take another hypothesis
        (Statement n' f' _) <- oneOf otherHs

        -- Try to match them
        matching <- oneOf . maybeToList $ match (removeExistentialQuantifiers consequent / vs ++ boundVars consequent) f'
        let matchedTerms = map (matching !) vs  --NB. allow arbitrary term here, not variable
            -- add a CannotSubstitute tag if none exists
            tags' = if null [() | CannotSubstitute _ <- tags]
                        then tags ++ [CannotSubstitute []]
                        else tags

        --make sure the substitution is not forbidden
        (CannotSubstitute tss, tagContext) <- oneOf $ eachElementWithContext tags'
        guard . not $ matchedTerms `elem` tss

        -- construct the retagged statement (and forbid the substitution)
        let h' = Statement n f . tagContext . return . CannotSubstitute $ tss ++ [matchedTerms]

        pd <- askPrintingData
        return (MoveDescription [] [] $
            "Note that one should not substitute $" ++ texTuple pd matchedTerms ++
            "$ into " ++ texSN n ++ ", as this would recreate the existing hypothesis " ++ texSN n' ++ ".",
                s $ Tableau tID tVs (context [h']) t)

    onTableau _ _ _ = mzero

--TODO: extract 66-76 into a 'tryToSubstitute' fn

tagRedundantBackwardsImplication :: MoveType
tagRedundantBackwardsImplication = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t@(Target [Left (Statement n' f' _)])) = do
        -- Find a one-variable implicative hypothesis (possibly using expansion)
        (Statement n f tags, context) <- oneOf $ eachElementWithContext hs
        UniversalImplies vs [antecedent] consequent <- return f <|> speculative (primaryExpansion f)
        let otherHs = context []

        -- Try to match the antecedent of the hypothesis with the target
        matching <- oneOf . maybeToList $ match (antecedent / vs ++ boundVars antecedent) f'
        let matchedTerms = map (matching !) vs  --NB. allow arbitrary term here, not variable
            -- add a CannotSubstitute tag if none exists
            tags' = if null [() | CannotSubstitute _ <- tags]
                        then tags ++ [CannotSubstitute []]
                        else tags

        --make sure the substitution is not forbidden
        (CannotSubstitute tss, tagContext) <- oneOf $ eachElementWithContext tags'
        guard . not $ matchedTerms `elem` tss

        -- construct the retagged statement (and forbid the substitution)
        let h' = Statement n f . tagContext . return . CannotSubstitute $ tss ++ [matchedTerms]

        pd <- askPrintingData
        return (MoveDescription [] [] $
            "Note that one will never substitute $" ++ texTuple pd matchedTerms ++
            "$ into " ++ texSN n ++ ", as this requires the use of the target " ++ texSN n' ++ " as a hypothesis.",
                s $ Tableau tID tVs (context [h']) t)
    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------


isSimpleConditional :: Formula -> Bool
isSimpleConditional (UniversalImplies _ as c) = all isAtomic as && isAtomic c
isSimpleConditional _ = False

{-
hypothesisDemands :: Statement -> [Variable]
hypothesisDemands (Statement _ f _) = nub . sort $
                                        boundUniversalVariablesInFormula f ++
                                        [v | v@(Variable _ _ _ True _) <- allVariablesInFormula f] --all bulleted vars

targetDemands :: Statement -> [Variable]
targetDemands (Statement _ f _) = nub . sort $
                                    boundExistentialVariablesInFormula f ++
                                    [v | v@(Variable _ _ _ True _) <- allVariablesInFormula f] --all bulleted vars
-}

typeOfVar :: Variable -> Type_
typeOfVar (Variable _ _ t _ _) = t

isOnlyTargetInItsTableau :: StatementName -> Tableau -> Bool
isOnlyTargetInItsTableau n = head . accumulateTableau shallow where
    shallow :: Tableau -> [Bool]
    shallow (Tableau _ _ _ (Target ps))
        | n `elem` [n' | Left (Statement n' _ _) <- ps] = [length ps == 1]
    shallow _ = []

--TODO: use memoisation to make this more efficient
deleteDangling :: MoveType
deleteDangling = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t@(Target ps)) = do

        let visibleHypotheses = filter undeleted $ inheritedHs ++ hypothesesAtAnyDepth tableau
            visibleTargets = filter undeleted $ targetFormulaeAtAnyDepth tableau

        --Pick a vulnerable hypothesis h
        (h@(Statement n f tags), context) <- oneOf $ eachUndeletedHypothesisWithContext hs
        guard $ Vulnerable `elem` tags

        --Pick a (unbound, unbulleted) variable v used in h
        v@(Variable _ _ vType VTNormal _) <- oneOf $ allVariablesInFormula f \\ boundVariablesInFormula f

        --Find all statements which meantion or could potentially use v
        let statementsWantingV = nub . sort $
              -- statements mentioning v [NB. mentions of v inside dependencies don't count -- hence use of allDirectVariablesInFormula.]
              [s | s@(Statement _ f' _) <- visibleHypotheses ++ visibleTargets, v `elem` allDirectVariablesInFormula f'] -- ++
--   --The following rule doesn't quite seem right; we have commented it out for now.
--              -- statements which are neither unexpandable nor simple-conditional
--              [s | s@(Statement _ f' _) <- visibleHypotheses ++ visibleTargets, not (isUnexpandable f' || isSimpleConditional f')] ++
              -- hypotheses demanding a variable of the same type as h
--              [s | s@(Statement _ f' _) <- visibleHypotheses, vType `elem` map typeOfVar (hypothesisDemands s)] ++
              -- targets demanding a variable of the same type as h
--              [s | s@(Statement _ f' _) <- visibleTargets, vType `elem` map typeOfVar (targetDemands s)]

        --TODO: If all the actualMatches lie in one tableau, move the hypothesis into that tableau
        pd <- askPrintingData
        case statementsWantingV \\ [h] of
            [] -> return (MoveDescription [] [] $ "Delete " ++ texSN n ++ " as no other statement mentions $" ++ tex pd v ++ "$.",
                          s $ Tableau tID tVs (context [tagAs Deleted h]) t)

            -- If h is only used by a single target statement t, and t is not the only target statement in its tableau
            --  move h down to t (By forming a new tableau)
            [targetStatement@(Statement n'@(StatementName STTarget _) _ _)] -> if isOnlyTargetInItsTableau n' tableau then mzero else do
                newTableau <- createTableau' False [tagAs (MovedDownFrom tID) h] $ Target [Left targetStatement]
                return (MoveDescription [] [] $ "Moved " ++ texSN n ++ " down, as $" ++ tex pd v ++ "$ can only be utilised by " ++ texSN n' ++ ".",
                          s . replaceTargetStatementWithTableau n' newTableau $ Tableau tID tVs (context []) t)

            _ -> mzero

    onTableau _ _ _ = mzero


----------------------------------------------------------------------------------------------------

deleteUnmatchable :: MoveType
deleteUnmatchable = movetypeFromSubmovetypes [
    deleteUnmatchableAtomicHypothesis,
    deleteHypothesisWithUnmatchablePremise,
    deleteHypothesisWithUnmatchableConclusion
  --TODO: add other submoves
  ]


--we want to define
--
--  matchesPremiseOf :: Statement -> Statement -> Bool
--  matchesPremiseOf s s': does s match premise of s' possibly after s is expanded?
--
--Unfortunately, we can't _expand_ unless we are in the RobotM monad
-- So instead we define
--
--   matchesPremiseOfM :: RobotM (Statement -> Statement -> Bool)
--
-- which returns the function we want.
-- (And similarly for other functions.)
-- Also note this ensures that this kind of speculative expansion can't affect the RobotM state

matchesPremiseOfM :: RobotM (Statement -> Statement -> Bool)
matchesPremiseOfM = do
    printingData <- askPrintingData
    library <- askLibrary
    robotState <- getRobotState
    let --tryMatchM nondeterministically tries to find a match, and returns () if it succeeds
        tryMatchM :: Statement -> Statement -> RobotM ()
        tryMatchM (Statement n f _) (Statement _ f' tags') = do
            -- Make sure the substitution is legal
            guard $ UsedForwardsWith [n] `notElem` tags'
            -- Possibly expand f' + look for a universal implication
            UniversalImplies v's as _ <- return f' <|> primaryExpansion f'
            -- Choose an antecedent
            a <- oneOf as
            -- Try to match
            m <- oneOf . maybeToList $ match (a / v's ++ boundVars a) f

            return ()

        tryMatch :: Statement -> Statement -> Bool
        tryMatch s = not . null . evalAllRobotM printingData library robotState . tryMatchM s

    return tryMatch


matchesPremiseOf'M :: RobotM (FormulaWithSlots -> Statement -> Bool)
matchesPremiseOf'M = do
    printingData <- askPrintingData
    library <- askLibrary
    robotState <- getRobotState
    let --tryMatchM nondeterministically tries to find a match, and returns () if it succeeds
        tryMatchM :: FormulaWithSlots -> Statement -> RobotM ()
        tryMatchM (FormulaWithSlots f vs) (Statement _ f' tags') = do
            -- Possibly expand f' + look for a universal implication
            UniversalImplies v's as _ <- return f' <|> primaryExpansion f'
            -- Choose an antecedent
            a <- oneOf as
            -- Try to match
            guard $ twoWayMatchExists (f / vs ++ boundVars f) (a / boundVars a)

            return ()

        tryMatch :: FormulaWithSlots -> Statement -> Bool
        tryMatch f = not . null . evalAllRobotM printingData library robotState . tryMatchM f

    return tryMatch


matchesConclusionOf'M :: RobotM (FormulaWithSlots -> Statement -> Bool)
matchesConclusionOf'M = do
    printingData <- askPrintingData
    library <- askLibrary
    robotState <- getRobotState
    let --tryMatchM nondeterministically tries to find a match, and returns () if it succeeds
        tryMatchM :: FormulaWithSlots -> Statement -> RobotM ()
        tryMatchM (FormulaWithSlots f vs) (Statement _ f' tags') = do
            -- Possibly expand f' + look for a universal implication
            UniversalImplies v's _ c <- return f' <|> primaryExpansion f'
            -- Try to match
            guard $ twoWayMatchExists (f / vs ++ boundVars f) (c / boundVars c)

            return ()

        tryMatch :: FormulaWithSlots -> Statement -> Bool
        tryMatch f = not . null . evalAllRobotM printingData library robotState . tryMatchM f

    return tryMatch

--we want to define
--
--  premiseMatchesFormula :: Formula -> [Variable] -> Statement -> Bool
--  premiseMatchesFormula f vs s: does a premise of s match f (with vs as wildcards in f), possibly after s is expanded?
--
--Unfortunately, we can't _expand_ unless we are in the RobotM monad
-- So instead we define
--
--   premiseMatchesFormulaM :: RobotM (Formula -> [Variable] -> Statement -> Bool)
--
-- which returns the function we want.
-- Also note this ensures that this kind of speculative expansion can't affect the RobotM state

--premiseMatchesFormulaM :: RobotM (Formula -> [Variable] -> Statement -> Bool)
--premiseMatchesFormulaM = do
--    robotState <- getRobotState
--    let --tryMatchM nondeterministically tries to find a match, and returns () if it succeeds
--        tryMatchM :: Formula -> [Variable] -> Statement -> RobotM ()
--        tryMatchM f vs (Statement _ f' tags') = do
--            -- Possibly expand f' + look for a universal Implication
--            UniversalImplies v's as _ <- return f' <|> primaryExpansion f'
--            -- Choose an antecedent
--            a <- oneOf as
--            -- Try to match
--            m <- oneOf . maybeToList $ twoWayMatch (a / v's ++ boundVars a) (f / vs)
--            let substituted = map (m !) v's  --the terms substituted into the UniversalImplies
--            -- Make sure the substitution is legal
--            guard $ null [() | CannotSubstitute tss <- tags', substituted `elem` tss]
--            return ()
--
--        tryMatch :: Formula -> [Variable] -> Statement -> Bool
--        tryMatch f vs s = not . null $ evalAllRobotM robotState (tryMatchM f vs s)
--
--    return tryMatch

{-
--matchesPremise tableau vs f s: does f (with vs as wildcards) match a premise of s, possibly after s is expanded?
matchesPremise :: Tableau -> [Variable] -> Formula -> Statement -> RobotM ()
matchesPremise tableau vs f (Statement _ f' tags) = do
    -- Possibly expand f' + look for a universal Implication
    UniversalImplies v's as _ <- return f' <|> primaryExpansion f'
    -- Choose an antecedent
    a <- oneOf as
    -- Try to match
    m <- oneOf . maybeToList $ twoWayMatch (a / v's ++ boundVars a) (f / vs)
    let substituted = map (m !) v's  --the terms substituted into the UniversalImplies
    -- Make sure the substitution is legal
    guard $ null [() | CannotSubstitute tss <- tags, substituted `elem` tss]

--matchesConclusion tableau vs f s: does f (with vs as wildcards)  match a conclusion of s, possibly after s is expanded?
matchesConclusion :: Tableau -> [Variable] -> Formula -> Statement -> RobotM ()
matchesConclusion tableau vs f (Statement _ f' tags) = do
    -- Possibly expand f' + look for a universal Implication
    UniversalImplies v's _ c <- return f' <|> primaryExpansion f'
    -- Try to match
    m <- oneOf . maybeToList $ twoWayMatch (c / v's ++ boundVars c) (f / vs)
    let substituted = map (m !) v's  --the terms substituted into the UniversalImplies
    -- Make sure the substitution is legal
    guard $ null [() | CannotSubstitute tss <- tags, substituted `elem` tss]
    return ()
-}

--matches f s: does f match s
matches :: FormulaWithSlots -> Statement -> Bool
matches (FormulaWithSlots f vs) (Statement _ f' _) =
    twoWayMatchExists (f / vs ++ boundVars f) (f' / boundVars f')


deleteUnmatchableAtomicHypothesis :: MoveType
deleteUnmatchableAtomicHypothesis = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t@(Target ps)) = do

        let visibleHypotheses = filter undeleted $ inheritedHs ++ hypothesesAtAnyDepth tableau
            visibleTargets = filter undeleted $ targetFormulaeAtAnyDepth tableau

        --Pick a vulnerable unexpandable atomic hypothesis with no bulleted variables
        (h@(Statement n f tags), context) <- oneOf $ eachUndeletedHypothesisWithContext hs
        guard $ Vulnerable `elem` tags
        guard $ isAtomic f
        guard =<< isUnexpandable f
        guard . null . filter isBulletedOrDiamonded $ allDirectVariablesInFormula f --no bulleted variable

        matchesPremiseOf <- matchesPremiseOfM

        let actualMatches = filter ((f/[]) `matches`) visibleTargets ++
                            filter (h `matchesPremiseOf`) visibleHypotheses

--        --TODO: If all the actualMatches lie in one tableau, move the hypothesis into that tableau
        case actualMatches of
            [] -> return (MoveDescription [] [] $ "Deleted " ++ texSN n ++ ", as this unexpandable atomic statement is unmatchable.",
                          s $ Tableau tID tVs (context [tagAs Deleted h]) t)

            [targetStatement@(Statement n'@(StatementName STTarget _) _ _)] -> if isOnlyTargetInItsTableau n' tableau then mzero else do
                newTableau <- createTableau' False [tagAs (MovedDownFrom tID) h] $ Target [Left targetStatement]
                return (MoveDescription [] [] $ "Moved " ++ texSN n ++ ", as this unexpandable atomic statement can only be used to prove " ++ texSN n' ++ ".",
                          s . replaceTargetStatementWithTableau n' newTableau $ Tableau tID tVs (context []) t)

            _ -> mzero

    onTableau _ _ _ = mzero


deleteHypothesisWithUnmatchablePremise :: MoveType
deleteHypothesisWithUnmatchablePremise = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t@(Target ps)) = do

        let visibleHypotheses = filter undeleted $ inheritedHs ++ hypothesesAtAnyDepth tableau
            visibleTargets = filter undeleted $ targetFormulaeAtAnyDepth tableau

        --Pick a vulnerable hypothesis
        (h@(Statement n f tags), context) <- oneOf $ eachUndeletedHypothesisWithContext hs
        guard $ Vulnerable `elem` tags

        --save the state before performning any expansions
        state <- getRobotState

        --make sure it's universal
        UniversalImplies vs as _ <- return f <|> primaryExpansion f
        -- Choose a premise/antecedent
        a <- oneOf as

        matchesPremiseOf' <- matchesPremiseOf'M
        matchesConclusionOf' <- matchesConclusionOf'M

        let actualMatches = filter ((a/vs) `matches`) [h | h@(Statement _ g _) <- visibleHypotheses, isAtomic g] ++
                            filter ((a/vs) `matchesConclusionOf'`) visibleHypotheses ++
                            filter ((a/vs) `matchesPremiseOf'`) visibleTargets

        --restore the state (so we don't use up any variable names)
        putRobotState state

--        --TODO: If all the actualMatches lie in one tableau, move the hypothesis into that tableau
        case actualMatches of
            [] -> return (MoveDescription [] [] $ "Deleted " ++ texSN n ++ ", as the premise of this implicative statement is unmatchable.",
                          s $ Tableau tID tVs (context [tagAs Deleted h]) t)

            [targetStatement@(Statement n'@(StatementName STTarget _) _ _)] -> if isOnlyTargetInItsTableau n' tableau then mzero else do
                newTableau <- createTableau' False [tagAs (MovedDownFrom tID) h] $ Target [Left targetStatement]
                return (MoveDescription [] [] $ "Moved " ++ texSN n ++ ", as the premise of this unexpandable atomic statement can only be used with " ++ texSN n' ++ ".",
                          s . replaceTargetStatementWithTableau n' newTableau $ Tableau tID tVs (context []) t)

            _ -> mzero

    onTableau _ _ _ = mzero



deleteHypothesisWithUnmatchableConclusion :: MoveType
deleteHypothesisWithUnmatchableConclusion = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t@(Target ps)) = do

        let visibleHypotheses = filter undeleted $ inheritedHs ++ hypothesesAtAnyDepth tableau
            visibleTargets = filter undeleted $ targetFormulaeAtAnyDepth tableau

        --Pick a vulnerable hypothesis
        (h@(Statement n f tags), context) <- oneOf $ eachUndeletedHypothesisWithContext hs
        guard $ Vulnerable `elem` tags

        --save the state before performning any expansions
        state <- getRobotState

        --make sure it's universal
        UniversalImplies vs _ c <- return f <|> primaryExpansion f

        matchesPremiseOf' <- matchesPremiseOf'M
        matchesConclusionOf' <- matchesConclusionOf'M

        let actualMatches = filter ((c/vs) `matches`) visibleTargets ++
                            filter ((c/vs) `matchesPremiseOf'`) visibleHypotheses ++
                            filter ((c/vs) `matchesConclusionOf'`) visibleTargets

        --restore the state (so we don't use up any variable names)
        putRobotState state

--        --TODO: If all the actualMatches lie in one tableau, move the hypothesis into that tableau
        case actualMatches of
            [] -> return (MoveDescription [] [] $ "Deleted " ++ texSN n ++ ", as the conclusion of this implicative statement is unmatchable.",
                          s $ Tableau tID tVs (context [tagAs Deleted h]) t)

            [targetStatement@(Statement n'@(StatementName STTarget _) _ _)] -> if isOnlyTargetInItsTableau n' tableau then mzero else do
                newTableau <- createTableau' False [tagAs (MovedDownFrom tID) h] $ Target [Left targetStatement]
                return (MoveDescription [] [] $ "Moved " ++ texSN n ++ ", as the premise of this unexpandable atomic statement can only be used with " ++ texSN n' ++ ".",
                          s . replaceTargetStatementWithTableau n' newTableau $ Tableau tID tVs (context []) t)

            _ -> mzero

    onTableau _ _ _ = mzero
