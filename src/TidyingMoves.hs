{-# LANGUAGE TupleSections #-}

module TidyingMoves (
    peelAndSplitUniversalConditionalTarget,
    peelBareUniversalTarget,
    flipNegativeTarget,
    flipNegativeHypothesis,
    splitConjunctiveTarget,
    splitDisjunctiveHypothesis,
    splitDisjunctiveTarget,
    removeTarget,
    collapseSubtableauTarget,
    automaticRewrite,
    rewriteVariableTermEquality,
    rewriteVariableVariableEquality
) where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List
import Data.Map ((!))
import Debug.Trace

import Prelude hiding ((/))
import Types
import Match
import Move
import TexBase
import Tex
import RobotM
import Expansion
import Writeup

----------------------------------------------------------------------------------------------------

-- If you peel a target that contains a bulleted variable,
--   note that the variable is independent of the Variables that were peeled

peelAndSplitUniversalConditionalTarget :: MoveType
peelAndSplitUniversalConditionalTarget = tableauwise onTableau where

    {- TODO: make this affect more cases with more than one target?-}
    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target [Left (Statement n (UniversalImplies vs as c) _)])) = do
        as' <- mapM (createStatement STHypothesis) $ markDependencies <$> as
        cs' <- mapM (createStatement STTarget) $ conjuncts c
        return (MoveDescription [n] [Let [vs `BeSuchThat` as']] $ "Apply `let' trick and move premise of universal-conditional target " ++ texSN n ++ " above the line.",
                markBulletedIndependencies vs . s $ Tableau tID (tVs ++ vs) (hs ++ as') (Target $ Left <$> cs'))
    onTableau _ _ _ = mzero

peelBareUniversalTarget :: MoveType
peelBareUniversalTarget = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target [Left (Statement n (Forall vs c) _)])) = do
        c' <- createStatement STTarget c
        return (MoveDescription [n] [Take vs] $ "pply `let' trick and move premise of universal target " ++ texSN n ++ " above the line.",
                markBulletedIndependencies vs . s $ Tableau tID (tVs ++ vs) hs (Target [Left c']))
    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------

flipNegativeTarget :: MoveType
flipNegativeTarget = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target [Left (Statement n (Not f) _)])) = do
        h' <- createStatement STHypothesis f
        return (MoveDescription [n] [StubClause "Move negative target"] $
                "Move negative target " ++ texSN n ++ " above the line and make it positive.",
                s $ Tableau tID tVs (hs ++ [h']) Contradiction)
    onTableau _ _ _ = mzero



flipNegativeHypothesis :: MoveType
flipNegativeHypothesis = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs Contradiction) = do
        (Statement n (Not f) _, context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        t <- createStatement STTarget f

        return (MoveDescription [n] [StubClause "Move negative hypothesis"] $
                "Move negative hypothesis " ++ texSN n ++ "  below the line and make it positive.",
                  s $ Tableau tID tVs (context []) (Target [Left t]))

    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------

splitConjunctiveTarget :: MoveType
splitConjunctiveTarget = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs t@(Target ps)) = do
        --pick a conjunctive target
        (Left (Statement n (And fs) _), context) <- oneOf $ eachUndeletedTargetPartWithContext ps

        --turn the conjuncts into new statements
        newTs <- mapM (createStatement STTarget) fs

        return (MoveDescription [n] [] $ "Split up conjunctive target " ++ texSN n ++ ".",
                s . Tableau tID tVs hs . Target . context $ Left <$> newTs)

    onTableau _ _ _ = mzero



splitDisjunctiveHypothesis :: MoveType
splitDisjunctiveHypothesis = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs t) = do
        --pick a disjunctive hypothesis
        (h@(Statement n (Or fs) _), context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        --turn the disjuncts into new tableaux
        disjunctHs <- mapM (createStatement STHypothesis) fs
        copiedTs <- mapM copyTarget [t | _ <- disjunctHs]
        newTableaux <- zipWithM (createTableau' False) (return <$> disjunctHs) copiedTs

        return (MoveDescription [n] [StubClause "Split disjunctive hypothesis"] $ "Split into cases to handle disjunctive hypothesis " ++ texSN n ++ ".",
                s . Tableau tID tVs (context []) . Target $ Right . return <$> newTableaux)

    onTableau _ _ _ = mzero


splitDisjunctiveTarget :: MoveType
splitDisjunctiveTarget = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do
        --pick a target part which is a single disjunctive statement
        (Left (Statement n (Or fs) _), context) <- oneOf $ eachUndeletedTargetPartWithContext ps

        --Create a new tableau for each disjunct:

        disjuncts <- mapM (createStatement STTarget) fs

        newTableaux <- mapM (createTableau' False []) (Target . return . Left <$> disjuncts) :: RobotM [Tableau]
        newTableaux' <- mapM copyTableau newTableaux  --rename all targets (inc. the disjuncts)


        return (MoveDescription [n] [StubClause "Split disjunctive target"] $ "Split up disjunctive target " ++ texSN n ++ ".",
                s . Tableau tID tVs hs . Target . context . return . Right $ newTableaux')

    onTableau _ _ _ = mzero

--splitDisjunctiveTarget :: MoveType
--splitDisjunctiveTarget = tableauwise onTableau where
--
--    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
--    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do
--        --pick a target part which is a single disjunctive statement
--        (Left (Statement n (Or fs) _), context) <- oneOf $ eachUndeletedTargetPartWithContext ps
--
--        --Create a new tableau for each disjunct:
--
--        let disjuncts = [Statement n {-<--sic-}  f [] | f <- fs]
--        -- note that we reuse the name n of the original statement here, because we will copy the _entirety_
--        -- of the new tableaux, so that targets other than n are renamed too.
--
--        newTableaux <- mapM (createTableau' []) (Target . context . return . Left <$> disjuncts) :: RobotM [Tableau]
--        newTableaux' <- mapM copyTableau newTableaux  --rename all targets (inc. the disjuncts)
--
--
--        return (MoveDescription [n] $ "Split disjunctive target " ++ texSN n ++ ".",
--                s . Tableau tID tVs hs . Target . return . Right $ newTableaux')
--
--    onTableau _ _ _ = mzero
----------------------------------------------------------------------------------------------------

removeTarget :: MoveType
removeTarget = movetypeFromSubmovetypes [
    matchTargetWithHypothesis,
    matchExistentialConjunctiveTargetWithHypotheses,
    matchSingleTargetWithBulletedHypothesis,
    matchBulletedTargets
  ]

matchTargetWithHypothesis :: MoveType
matchTargetWithHypothesis = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs (Target ps)) = do
        --pick a hypothesis
        (Statement n f _, context) <- oneOf . eachUndeletedHypothesisWithContext $ hs ++ inheritedHs

        --and a target
        (Left (Statement n' f' _), targetContext) <- oneOf $ eachUndeletedTargetPartWithContext ps

        -- Try to match hypothesis and target
        matching <- oneOf . maybeToList $ match (f / boundVariablesInFormula f) f'

        case targetContext [] of
            [] ->  return (MoveDescription [n, n'] [ProofDone] $
                           "Hypothesis " ++ texSN n ++ " matches target " ++ texSN n' ++ "," ++
                           " so " ++ texTN tID ++ " is done.",
                           s $ Done tID)

            ps' -> return (MoveDescription [n, n'] [] $
                           "Hypothesis " ++ texSN n ++ " matches target " ++ texSN n' ++ "," ++
                           " so we can remove " ++ texSN n' ++ ".",
                           s . Tableau tID tVs hs $ Target ps')

    onTableau _ _ _ = mzero

isTrivialEquality :: Formula -> Bool
isTrivialEquality (AtomicFormula (Predicate "equals") [t,t']) = t == t'
isTrivialEquality _ = False

matchExistentialConjunctiveTargetWithHypotheses :: MoveType
matchExistentialConjunctiveTargetWithHypotheses = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s (Tableau tID tVs hs (Target ps)) = do
        --find a target
        (Left t@(Statement n' f' _), targetContext) <- oneOf $ eachUndeletedTargetPartWithContext ps

        --which is existential
        (Exists vs g', expanded) <- return (f', False) <|> ((,True) <$> speculative (primaryExpansion f'))

        --match some of the conjuncts against the undeleted hypotheses
        (matching, ns, leftovers) <- matchSomeOfFormulaeAmongStatements vs (conjuncts g') . filter undeleted $ hs ++ inheritedHs

        --substitute into the leftover conjuncts
        let leftovers' = transform matching <$> leftovers

        --make sure the (substituted) leftover conjuncts are all trivial equalities
        guard $ all isTrivialEquality leftovers'

        pd <- askPrintingData
        let choices = [VariableChoice v (matching ! v) | v <- vs]
            message = "All conjuncts of " ++ texSN n' ++ (guard expanded >> " (after expansion)") ++
                      " can be simultaneously matched against " ++ texList (texSN <$> ns) ++
                      " or rendered trivial by choosing " ++ texList (tex pd <$> choices)

            proofClauses = if expanded then [TargetIs [t], ClearlyTheCaseDone]
                                       else [ThereforeSettingDone choices]

        case targetContext [] of
            [] ->  return (MoveDescription (ns ++ [n']) proofClauses $
                           message ++ ", so " ++ texTN tID ++ " is done.",
                           s $ Done tID)

            ps' -> return (MoveDescription (ns ++ [n']) [StubClause "remove one existential target"] $
                           message ++ ", so we can remove " ++ texSN n' ++ ".",
                           s . Tableau tID tVs hs $ Target ps')

    onTableau _ _ _ = mzero

--disjunctivePartsOfTargetOf tableau:
--find the (possibly nested) disjunctive targets of the tableau,
--  failing if you ever see conjunctive targets
disjunctivePartsOfTargetOf :: Tableau -> Maybe [Statement]
disjunctivePartsOfTargetOf (Tableau _ _ _ (Target [p])) = onPart p where
    onPart :: Either Statement [Tableau] -> Maybe [Statement]
    onPart (Left s) = Just [s]
    onPart (Right ts) = concat <$> mapM disjunctivePartsOfTargetOf ts where
disjunctivePartsOfTargetOf t = Nothing

matchSingleTargetWithBulletedHypothesis :: MoveType
matchSingleTargetWithBulletedHypothesis = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t) = do
        let bulletedVars = filter isBulletedOrDiamonded tVs

        --pick a hypothesis
        (Statement n f _, context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        -- if the targets of the tableau are morally a simple disjunction, extract them.
        disjunctiveTargets <- oneOf . maybeToList $ disjunctivePartsOfTargetOf tableau

        --pick any one of these targets
        Statement n' f' _ <- oneOf disjunctiveTargets

        -- Try to match hypothesis and target
        matching <- oneOf . maybeToList $ match (f / boundVariablesInFormula f ++ bulletedVars) f'

        let choices = [VariableChoice v (matching ! v) | v <- bulletedVars]
        guard $ all isBulletedVariableChoiceLegal choices

        pd <- askPrintingData
        return (MoveDescription [n, n'] [ThereforeSettingDone choices] $
                   "Hypothesis " ++ texSN n ++ " matches target " ++ texSN n' ++ " after choosing " ++
                   texList (tex pd <$> choices) ++ ", so " ++
                   texTN tID ++ " is done.",
                s $ Done tID)

    onTableau _ _ _ = mzero

--foldM :: Monad m => (Matching -> b -> m Matching) -> Matching -> [b] -> m Matching

matchBulletedTargets :: MoveType
matchBulletedTargets = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs (Target ps)) = do
        let bulletedVars = filter isBulletedOrDiamonded tVs
            visibleHs = filter undeleted $ hs ++ inheritedHs

            extend :: [Statement] -> Matching -> Either Statement [Tableau] -> RobotM Matching
            extend hs m (Left (Statement _ f' _)) = do
                --pick a hypothesis
                (Statement n f _, context) <- oneOf $ eachUndeletedHypothesisWithContext hs

                -- Try to match hypothesis and target
                oneOf . maybeToList $ extendMatch m (f' / boundVariablesInFormula f' ++ bulletedVars) f

            extend hs m (Right tableau's) = do
                --pick a disjunct
                (Tableau _ _ h's (Target p's)) <- oneOf tableau's

                --match against its target parts (using its extra hypotheses)
                foldM (extend $ hs ++ h's) m p's

        matching <- foldM (extend visibleHs) emptyMatching ps

        let choices = [VariableChoice v (matching ! v) | v <- bulletedVars]
        guard $ all isBulletedVariableChoiceLegal choices

        pd <- askPrintingData
        return (MoveDescription [] [ThereforeSettingDone choices] $
                   "Choosing " ++ texList (tex pd <$> choices) ++
                   " matches all targets inside " ++ texTN tID ++ " against hypotheses," ++
                   " so " ++ texTN tID ++ " is done.",
                s $ Done tID)

    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------

collapseSubtableauTarget :: MoveType
collapseSubtableauTarget = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s (Tableau tID tVs hs (Target ps)) = do
        --pick a target (Target p's) which is a subtableau with no (undeleted) hypotheses
        --  *and* owns no variables
        (Right [Tableau tID' [] h's (Target p's)], context) <- oneOf $ eachUndeletedTargetPartWithContext ps
        guard $ all deleted h's

        return (MoveDescription [] [] $ "Collapsed subtableau " ++ texTN tID' ++ " as it has no undeleted hypotheses.",
                s . Tableau tID tVs hs . Target $ context p's)

    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------


automaticRewrite :: MoveType
automaticRewrite = movetypeFromSubmovetypes [
    automaticRewriteHypothesis,
    automaticRewriteTarget
  ]

automaticRewriteHypothesis :: MoveType
automaticRewriteHypothesis = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs t) = do
        --pick a hypothesis
        (Statement n f _, context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        --obtain its rewrite (if one exists)
        rewritten <- rewriteFormula f
        expansion <- oneOf $ maybeToList rewritten

        newHypothesis <- createStatement STHypothesis expansion
        return (MoveDescription [n] [] $ "Rewrite terms in hypothesis " ++ texSN n ++ ".",
            s $ Tableau tID tVs (context [newHypothesis]) t)

    onTableau _ _ _ = mzero

automaticRewriteTarget :: MoveType
automaticRewriteTarget = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do
        --pick a target
        (Left (Statement n f _), context) <- oneOf $ eachUndeletedTargetPartWithContext ps

        --obtain its rewrite (if one exists)
        rewritten <- rewriteFormula f
        expansion <- oneOf $ maybeToList rewritten

        newTarget <- createStatement STTarget expansion
        return (MoveDescription [n] [] $ "Rewrite terms in target " ++ texSN n ++ ".",
            s . Tableau tID tVs hs . Target $ context [Left newTarget])

    onTableau _ _ _ = mzero


rewrite :: Term -> Variable -> Formula -> Formula
rewrite t v = mapTermInFormula onTerm where
    onTerm :: Term -> Term
    onTerm t' | t' == t = VariableTerm v
              | otherwise = t'


rewriteEquality :: (Formula -> [(Variable,Term)]) -> MoveType
rewriteEquality extract = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do
        --pick a hypothesis
        (h@(Statement n f _), context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        --pick v,t s.t. we can rewrite t -> v
        (v,t) <- oneOf $ extract f

        guard $ v `notElem` allVariablesInTerm t

        let rewriteStatement :: StatementType -> Statement -> RobotM Statement
            rewriteStatement st s@(Statement n' f' tags) =
              let rewritten = rewrite t v f' in
                  if f' == rewritten then return s
                                     else createStatement st rewritten

        let rewriteTableau :: Tableau -> RobotM Tableau
            rewriteTableau = return . mapFormulaInTableau (rewrite t v)

        let g :: Either Statement [Tableau] -> RobotM (Either Statement [Tableau])
            g = either (liftM Left . rewriteStatement STTarget) (liftM Right . mapM rewriteTableau)

        hs' <- mapM (rewriteStatement STHypothesis) $ context []
        --remove any duplicates of old hypotheses
        let oldFormulae = [f | Statement _ f _ <- hs]
            hs'' = [h | h@(Statement _ f _) <- hs', h `elem` hs || f `notElem` oldFormulae]

        let rewrittenHs = hs'' \\ hs
        guard . not $ null rewrittenHs

        target' <- liftM Target $ mapM g ps

        pd <- askPrintingData
        return (MoveDescription [n] [since [h] $ Assertion rewrittenHs] $
                "Rewrite $" ++ tex pd t ++ "$ as $" ++ tex pd v ++ "$ throughout the tableau using hypothesis " ++ texSN n ++ ".",
            s $ Tableau tID tVs hs'' target')

    onTableau _ _ _ = mzero


rewriteVariableTermEquality = rewriteEquality extract where
    extract :: Formula -> [(Variable,Term)]
    extract (AtomicFormula (Predicate "equals") [vt@(VariableTerm v), v't@(VariableTerm v')]) = [(v,v't), (v',vt)]
    extract (AtomicFormula (Predicate "equals") [VariableTerm v, t]) = [(v,t)]
    extract (AtomicFormula (Predicate "equals") [t, VariableTerm v]) = [(v,t)]
    extract _ = []

rewriteVariableVariableEquality = rewriteEquality extract where
    extract (AtomicFormula (Predicate "equals") [vt@(VariableTerm v), v't@(VariableTerm v')]) = [(v,v't), (v',vt)]
    extract _ = []
