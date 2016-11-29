{-# LANGUAGE TupleSections #-}

module ApplyingMoves (
    expandPreExistentialHypothesis,
    expandPreUniversalTarget,
    expandPreExistentialTarget,
    elementaryExpansionOfHypothesis,
    elementaryExpansionOfTarget,
    forwardsReasoning,
    forwardsLibraryReasoning,
    backwardsReasoning,
    backwardsLibraryReasoning,
    solveBullets
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
import Debug.Trace

import Types
import Move
import Match
import Expansion
import TexBase
import Tex
import RobotM
import Library
import Writeup

--TODO: rename tID to tN in this and other files

----------------------------------------------------------------------------------------------------

boundVars =  boundVariablesInFormula

----------------------------------------------------------------------------------------------------

--peelHypothesis: peels a hypothesis and also splits 'and's recursively to any depth.
-- also returns list of peeled variables.
peelHypothesis :: Formula -> ([Formula], [Variable])
peelHypothesis f@(AtomicFormula _ _) = ([f], [])
peelHypothesis f@(Not _) = ([f], [])
peelHypothesis f@(And fs) = concat *** concat $ unzip (peelHypothesis <$> fs)
peelHypothesis f@(Or _) = ([f], [])
peelHypothesis f@(Forall _ _) = ([f], [])
peelHypothesis f@(UniversalImplies _ _ _) = ([f], [])
peelHypothesis f@(Exists vs f') = second (++ vs) $ peelHypothesis f'

----------------------------------------------------------------------------------------------------

isExistential :: Formula -> Bool
isExistential f@(Exists _ _) = True
isExistential _ = False

isUniversal ::  Formula -> Bool
isUniversal (Forall _ _) = True
isUniversal (UniversalImplies _ _ _) = True
isUniversal _ = False

expandPreUniversalTarget :: MoveType
expandPreUniversalTarget = tableauwise onTableau where

    {- TODO: make this affect more cases with more than one target?-}
    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target [Left (Statement n f _)])) = do
        --obtain the primary expansion of the target (if one exists)
        expansion <- primaryExpansion f

        --make sure it's pre-uc
        guard $ isUniversal expansion

        f'' <- createStatement STTarget expansion
        return (MoveDescription [n] [] $ "Expand pre-universal target " ++ texSN n ++ ".", s $ Tableau tID tVs hs (Target [Left f'']))

    onTableau _ _ _ = mzero


expandPreExistentialTarget :: MoveType
expandPreExistentialTarget = tableauwise onTableau where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target ps)) = do
        --pick a target
        (Left (Statement n f _), context) <- oneOf $ eachUndeletedTargetPartWithContext ps

        --obtain the primary expansion of the target (if one exists)
        expansion <- primaryExpansion f

        --make sure it's pre-existential
        guard $ isExistential expansion

        f'' <- createStatement STTarget expansion

        return (MoveDescription [n] [TargetIs [f'']] $ "Expand pre-existential target " ++ texSN n ++ ".",
                    s . Tableau tID tVs hs . Target . context . return . Left $ f'')

    onTableau _ _ _ = mzero


expandPreExistentialHypothesis :: MoveType
expandPreExistentialHypothesis = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs t) = do
        --pick a hypothesis
        (h@(Statement n f _), context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        --obtain its primary expansion (if one exists)
        expansion <- markDependencies <$> primaryExpansion f

        --make sure it's pre-existential
        guard $ isExistential expansion

        let (newFormulae, vs) = peelHypothesis expansion
        newHypotheses <- mapM (createStatement STHypothesis) newFormulae :: RobotM [Statement]
        return (MoveDescription [n] [byDefSince [h] . existVars vs $ Assertion newHypotheses] $ "Expand pre-existential hypothesis " ++ texSN n ++ ".",
                    s $ Tableau tID (tVs ++ vs) (context newHypotheses) t)
    onTableau _ _ _ = mzero


----------------------------------------------------------------------------------------------------


partsOfElementary :: Formula -> [Formula]
partsOfElementary f@(AtomicFormula _ _) = [f]
partsOfElementary f@(Not _) = [f]
partsOfElementary (And fs) = fs
partsOfElementary f@(Or _) = [f]


elementaryExpansionOfHypothesis :: MoveType
elementaryExpansionOfHypothesis = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs t) = do
        --pick a hypothesis
        (h@(Statement n f _), context) <- oneOf $ eachUndeletedHypothesisWithContext hs

        --obtain its primary expansion (if one exists)
        expansion <- markDependencies <$> primaryExpansion f

        --make sure it's elementary
        guard $ isAtomic expansion

        newHypotheses <- mapM (createStatement STHypothesis) (partsOfElementary expansion) :: RobotM [Statement]
        return (MoveDescription [n] [since [h] $ Assertion newHypotheses] $ "Quantifier-free expansion of hypothesis " ++ texSN n ++ ".",
                   s $ Tableau tID tVs (context newHypotheses) t)

    onTableau _ _ _ = mzero

elementaryExpansionOfTarget :: MoveType
elementaryExpansionOfTarget = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tN@(TableauName isUnlocked _) tVs hs (Target ps)) = do
        --pick a target
        (Left t@(Statement n f _), context) <- oneOf $ eachUndeletedTargetPartWithContext ps

        --obtain its primary expansion (if one exists)
        expansion <- primaryExpansion f

        --make sure it's elementary
        guard $ isAtomic expansion

        newTargetStatements <- mapM (createStatement STTarget) (partsOfElementary expansion) :: RobotM [Statement]

        let proofClauses = if isUnlocked then [But $ [t] `Iff` newTargetStatements]
                                         else [TargetIsIE [t] newTargetStatements]

        return (MoveDescription [n] proofClauses $ "Quantifier-free expansion of target " ++ texSN n ++ ".",
                    s . Tableau tN tVs hs . Target . context $ Left <$> newTargetStatements)

    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------

--the heart of a formula is the part that remains when you remove all existential/bare-universal
--  quantifiers. So e.g. the heart of ∀x,ϵ.(∃δ.(∀y.(d(x,y) < δ ⇒ d(f(x),f(y)) < ϵ)))
--   is ∀y.(d(x,y) < δ ⇒ d(f(x),f(y)) < ϵ)
--Looking at this is useful when performing backwards reasoning.
--This function computes the heart, and also
-- a) which ∀ variables which were removed (x,ϵ,y in above)
-- b) which ∃ variables which were removed (δ in above)

heartAndVariables :: Formula -> (Formula, [Variable], [Variable])
heartAndVariables f@(AtomicFormula _ _) = (f,[],[])
heartAndVariables f@(Not _) = (f,[],[])
heartAndVariables f@(And fs) = (f,[],[])
heartAndVariables f@(Or _) = (f,[],[])
heartAndVariables (Forall vs f') = (g,us++vs,es) where (g,us,es) = heartAndVariables f'
heartAndVariables f@(UniversalImplies _ _ _) = (f,[],[])
heartAndVariables (Exists vs f') =  (g,us,es++vs) where (g,us,es) = heartAndVariables f'

--peelAndFilterNotIn fs f': peel f', and return the parts if at least one of them is not in fs
--  also return any peeled variables
peelAndFilterNotIn :: [Formula] -> Formula -> Maybe ([Formula], [Variable])
peelAndFilterNotIn fs f' =
    let (f's, vs) = peelHypothesis f'
        bound = boundVariablesInFormula f'
        already_there :: Formula -> Bool
        already_there g = any (isIsomorphic bound g) fs

    in  guard (not (already_there f') && not (any already_there f's)) >> return (f's, vs)

--TODO: in forwards/backwarsd reasoning,
-- at the moment we only handle the case where the implication has exactly one antecedent
--  although this should be easy to get around using recursion or currying

areDistinct :: Ord a => [a] -> Bool
areDistinct as = length as == length (nub . sort $ as)

statementsByName :: [StatementName] -> [Statement] -> [Statement]
statementsByName ns ss = [s | s@(Statement n _ _) <- ss, n `elem` ns]

hasNoDiamondedVariables :: Statement -> Bool
hasNoDiamondedVariables (Statement _ f _) = null [v | v@(Variable _ _ _ VTDiamond _) <- allVariablesInFormula f]

isUnlocked :: Tableau -> Bool
isUnlocked (Tableau (TableauName u _) _ _ _) = u

--TODO: Other submoves of forward reasoning need to be implemented
forwardsReasoning :: MoveType
forwardsReasoning = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tN tVs hs t) = do
        -- Find a (possibly inherited) hypothesis with an implicative heart (possibly using expansion)
        --   also obtain any variables lying outside the heart
        (h@(Statement n f tags), context) <- oneOf $ eachUndeletedHypothesisWithContext hs ++
                                                  [(h', const hs) | h' <- inheritedHs]
        guard $ hasNoDiamondedVariables h

        (UniversalImplies vs as c, uvs, evs) <-
            heartAndVariables <$> (return f <|> (markDependencies <$> speculative (allExpansions f)))
            --NB 'speculative' expansion doesn't claim var. names for bound vars  in expanded
            --  implication, as such vars will not appear in the new statements generated
        let otherHs = context []
            visibleHs = filter hasNoDiamondedVariables . filter undeleted $ otherHs ++ inheritedHs

        -- Try to match the antecedents
        (matching, n's) <- matchFormulaeAmongStatements (uvs ++ vs) as visibleHs
        guard $ areDistinct n's

        --make sure we have matched all the quantified variables
        guard . all (`Map.member` matching) $ uvs ++ vs

        let sortedN's = sort n's

            allLocalHNames = [name | Statement name _ _ <- hs]
            --local: names of used hypotheses from this tableau (i.e. not inherited)
            local = filter (`elem` allLocalHNames) (n:sortedN's)

        --make sure at least one of implication, statements used is not inherited
        guard . not $ null local

        --make sure the substitution hasn't been done before
        guard . not $ UsedForwardsWith sortedN's  `elem` tags

        --make the corresponding subsitutions in the consequent
        let newH = transform matching c

        --obtain the fresh parts of the substituted consequent, aborting if there are none
        (partsFormulae, vs') <- oneOf . maybeToList $ peelAndFilterNotIn [g | (Statement _ g _) <- hs] newH
        parts <- mapM (createStatement STHypothesis) $ markDependencies <$> partsFormulae :: RobotM [Statement]

        return (MoveDescription (n:n's) [since (h:statementsByName n's visibleHs) . existVars (evs ++ vs') $ Assertion parts] $
                    "Forwards reasoning using " ++ texSN n ++ " with " ++ texSNs n's ++ ".",
                    tagStatementInTableauAs (UsedForwardsWith sortedN's) n .
                    flip (foldr (tagStatementInTableauAs Vulnerable)) {-local-} (n:n's) .
                    s $
                    Tableau tN (tVs ++ evs ++ vs') (hs ++ parts) t)
    onTableau _ _ _ = mzero


forwardsLibraryReasoning :: MoveType
forwardsLibraryReasoning = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tN tVs hs t) = do
        -- Find a (possibly inherited) hypothesis with an implicative heart (possibly using expansion)
        Result desc as c <- askLibraryResult
        let vs = concatMap allDirectVariablesInFormula as
            visibleHs = filter hasNoDiamondedVariables . filter undeleted $ hs ++ inheritedHs

        -- Try to match the antecedents (a.k.a. premises)
        (matching, n's) <- matchFormulaeAmongStatements vs as $ visibleHs
        guard $ areDistinct n's

        --make sure we have matched all the quantified variables
        guard $ all (`Map.member` matching) vs

        let sortedN's = sort n's

            allLocalHNames = [name | Statement name _ _ <- hs]
            --local: names of used hypotheses from this tableau (i.e. not inherited)
            local = filter (`elem` allLocalHNames) sortedN's

        --make sure at least one of implication, statements used is not inherited
        guard . not $ null local

        -- Make the corresponding subsitutions in the consequent
        let newH = transform matching c

        --obtain the fresh parts of the substituted consequent, aborting if there are none
        (partsFormulae, vs') <- oneOf . maybeToList $ peelAndFilterNotIn [g | (Statement _ g _) <- hs] newH
        parts <- mapM (createStatement STHypothesis) $ markDependencies <$> partsFormulae :: RobotM [Statement]

        
        let newTerms = concatMap (accumulateTermInFormula return) [f | Statement _ f _ <- parts] :: [Term]
        let globalTerms = accumulateTermInTableau return $ s tableau :: [Term]

        --make sure there are no new terms
        guard $ all (`elem` globalTerms) newTerms --

        return (MoveDescription n's [since (statementsByName n's visibleHs) . existVars vs' $ Assertion parts] $
                    "Forwards reasoning using library result ``" ++ desc ++ "'' with " ++ texSNs n's ++ ".",
                    flip (foldr (tagStatementInTableauAs Vulnerable)) {-local-} n's .
                    s $
                    Tableau tN (tVs ++ vs') (hs ++ parts) t)
    onTableau _ _ _ = mzero

--TODO: Other submoves of backward reasoning need to be implemented
backwardsReasoning :: MoveType
backwardsReasoning = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tN tVs hs t@(Target ps)) = do
        -- Find a (possibly inherited) hypothesis with an implicative heart (possibly using expansion)
        --   also obtain any variables lying outside the heart
        (h@(Statement n f tags), context) <- oneOf $ eachUndeletedHypothesisWithContext hs ++
                                                  [(h', const hs) | h' <- inheritedHs]
        guard $ hasNoDiamondedVariables h
--        (UniversalImplies vs as c, uvs, evs) <-
--            heartAndVariables <$> (return f <|>
--                                   (markDependencies <$> speculative (allExpansions f)))

        ((UniversalImplies vs as c, uvs, evs), expanded) <-
            first heartAndVariables <$> (return (f, False) <|>
                                         ((, True) . markDependencies <$> speculative (allExpansions f)))


            --NB 'speculative' expansion doesn't claim var. names for bound vars  in expanded
            --  implication, as such vars will not appear in the new statements generated
        let otherHs = context []
            visibleHs = filter hasNoDiamondedVariables . filter undeleted $ otherHs ++ inheritedHs

        -- Take a target statement
        (Left t@(Statement n' f' _), targetContext) <- oneOf $ eachUndeletedTargetPartWithContext ps

        -- Try to match the conclusion
        matching <- oneOf . maybeToList $ match (c / uvs ++ vs ++ boundVars c) f'
        -- Try to match all but one of the antecedents
        (matching', n''s, leftoverA) <- extendMatchAllButOneOfFormulaeAmongStatements matching (uvs ++ vs) as visibleHs
        guard $ areDistinct n''s

        --make sure we have matched all the quantified variables
        guard . all (`Map.member` matching') $ uvs ++ vs

--        let sortedN's = sort $ n' : n's

--            allLocalNames = n':[name | Statement name _ _ <- hs]
--            --local: names of used hypotheses/target from this tableau (i.e. not inherited)
--            local = filter (`elem` allLocalNames) (n:sortedN's)

        --make the corresponding subsitutions in the leftover antecedent
        let newT = transform matching' leftoverA

        --obtain the fresh parts of the substituted antecedent, aborting if there are none
        (partsFormulae, vs') <- oneOf . maybeToList $ peelAndFilterNotIn [g | (Statement _ g _) <- lefts ps] newT
        parts <- mapM (createStatement STTarget) partsFormulae :: RobotM [Statement]

        let ifOrWhenever = if isUnlocked tableau then Whenever else If

            writeupClauses = if expanded then [since (h:statementsByName n''s visibleHs) . existVars (evs ++ vs') $ parts `ifOrWhenever` t]
                                         else [since (statementsByName n''s visibleHs) . weKnowThat . existVars (evs ++ vs') $ parts `ifOrWhenever` t]

        return (MoveDescription (n:n':n''s) writeupClauses $
                    "Backwards reasoning using " ++ texSN n ++ " with " ++ texSNs (n':n''s) ++ ".",
                    flip (foldr (tagStatementInTableauAs Vulnerable)) {-local-}(n:n''s) .
                    s . Tableau tN (tVs ++ evs ++ vs') hs . Target . targetContext $ Left <$> parts)

    onTableau _ _ _ = mzero


--TODO: Other submoves of backward reasoning need to be implemented
backwardsLibraryReasoning :: MoveType
backwardsLibraryReasoning = tableauwise onTableau  where

    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tN tVs hs t@(Target ps)) = do
        -- Take a library result
        Result desc as c <- askLibraryResult
        let vs = concatMap allDirectVariablesInFormula as
            visibleHs = filter hasNoDiamondedVariables . filter undeleted $ hs ++ inheritedHs

        -- Take a target statement
        (Left targetS@(Statement n' f' _), targetContext) <- oneOf $ eachUndeletedTargetPartWithContext ps

        -- Try to match the conclusion
        matching <- oneOf . maybeToList $ match (c / vs ++ boundVars c) f'
        -- Try to match all but one of the antecedents (a.k.a. premises)
        (matching', n''s, leftoverA) <- extendMatchAllButOneOfFormulaeAmongStatements matching vs as visibleHs
        guard $ areDistinct n''s

        --make sure we have matched all the quantified variables
        guard $ all (`Map.member` matching') vs

--        let sortedN's = sort $ n' : n's
--
--            allLocalNames = n':[name | Statement name _ _ <- hs]
--            --local: names of used hypotheses/target from this tableau (i.e. not inherited)
--            local = filter (`elem` allLocalNames) sortedN's

        --make the corresponding subsitutions in the leftover antecedent
        let newT = transform matching' leftoverA

        --obtain the fresh parts of the substituted antecedent, aborting if there are none
        (partsFormulae, vs') <- oneOf . maybeToList $ peelAndFilterNotIn [g | (Statement _ g _) <- lefts ps] newT
        parts <- mapM (createStatement STTarget) partsFormulae :: RobotM [Statement]

        let ifOrWhenever = if isUnlocked tableau then Whenever else If

            writeupClauses = [since (statementsByName n''s visibleHs) . existVars vs' $  parts `ifOrWhenever` targetS]

        return (MoveDescription (n':n''s) writeupClauses $
                    "Backwards reasoning using library result ``" ++ desc ++ "'' with " ++ texSNs (n':n''s) ++ ".",
                    flip (foldr (tagStatementInTableauAs Vulnerable)) {-local-}n''s .
                    s . Tableau tN (tVs ++ vs') hs . Target . targetContext $ Left <$> parts)

    onTableau _ _ _ = mzero

----------------------------------------------------------------------------------------------------

--TODO: check we want VTBullet here

extractVarFromVarTerm :: Term -> Maybe Variable
extractVarFromVarTerm (VariableTerm v@(Variable _ _ _ VTBullet _)) = Just v
extractVarFromVarTerm _ = Nothing

--TODO: tidy up variable names in this next function
solveBullets :: MoveType
solveBullets = tableauwise onTableau  where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s tableau@(Tableau tID tVs hs t@(Target ps)) = do
        let bulletedVars = filter isBulletedOrDiamonded tVs -- [v | v@(Variable _ _ _ VTBullet _) <- tVs]
            varsInHypotheses = nub . sort $ concatMap allVariablesInFormula [f | Statement _ f _ <- hs]
            bulletedVarsBelowLine = bulletedVars \\ varsInHypotheses

        --need at one bulleted var which only occurs below the line
        guard . not $ null bulletedVarsBelowLine

        --all targets must be statements, not subtableax. (Relax this constraint?)
        guard $ all isLeft ps
        let targets = lefts ps

        (Solution vs fs sols) <- askLibrarySolution

        (matching, targetsMatched) <- matchFormulaeAmongStatements (concatMap allVariablesInFormula fs) fs targets

        --make sure we have matched all the targets
        guard $ length (nub . sort $ targetsMatched) == length targets

        --find the quantities each slot in the solution was matched against
        let ts = [matching ! v | v <- vs]

        -- make sure that they are all single variables
        v's <- oneOf . maybeToList $ mapM extractVarFromVarTerm ts

        -- make sure that they are all bulleted variables below the line
        guard $ all (`elem` bulletedVarsBelowLine) v's

        let choices = zipWith VariableChoice v's (transformTerm matching <$> sols)
        guard $ all isBulletedVariableChoiceLegal choices

        pd <- askPrintingData
        return (MoveDescription [] [WeMayTake choices, ProofDone] $
                   "Taking " ++
                   texList (tex pd <$> choices) ++ " matches all targets against a library solution, so " ++
                   texTN tID ++ " is done.",
                s $ Done tID)

    onTableau _ _ _ = mzero
