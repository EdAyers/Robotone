module Suspension (
    unlockExistentialUniversalConditionalTarget,
    unlockExistentialTarget,
    convertDiamondToBullet
) where

import Control.Applicative
import Control.Monad

import TexBase
import Types
import Move
import Tex
import RobotM
import Writeup

----------------------------------------------------------------------------------------------------

addDiamond :: Variable -> Variable
addDiamond (Variable n id t VTNormal ds) = Variable n id t VTDiamond ds
addDiamond _ = error "Attempt to add a diamond to a variable that already has a diamond."

addDiamondsInTableau :: [Variable] -> Tableau -> Tableau
addDiamondsInTableau vs = mapVariableInTableau shallow where
    shallow v@(Variable n id t VTNormal ds) | v `elem` vs = Variable n id t VTDiamond ds
    shallow v = v


--  If the target is existential-universal-conditional, then unlock it to create a diamonded tableau.
unlockExistentialUniversalConditionalTarget :: MoveType
unlockExistentialUniversalConditionalTarget = tableauwise onTableau where

    {- TODO: make this affect more cases with more than one target?-}
    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target [Left t@(Statement n (
        Exists evs (ui@(UniversalImplies uvs as c))
        ) _)])) = do
            as' <- mapM (createStatement STHypothesis) $ markDependencies <$> as
            cs' <- mapM (createStatement STTarget) $ conjuncts c
            newTableau@(Tableau tID' tVs' hs' t') <- createTableau' True (tagAs (MovedDownFrom tID) <$> as') $ Target (Left <$> cs')
            let newTableau' = Tableau tID' (tVs' ++ evs ++ uvs) hs' t'
--            ui' <- createStatement STTarget ui
            return (MoveDescription [n] [TargetIs [t] {-,Let [Suspended $ addDiamond <$> vs]-}] $
                        "Unlock existential-universal-conditional target " ++ texSN n ++ ".",
                        markBulletedIndependencies uvs . s . addDiamondsInTableau evs $ Tableau tID tVs hs (Target  [Right [newTableau']]))
    onTableau _ _ _ = mzero

--  If the target is existential, then unlock it to create a diamonded tableau.
unlockExistentialTarget :: MoveType
unlockExistentialTarget = tableauwise onTableau where

    {- TODO: make this affect more cases with more than one target?-}
    onTableau :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau _ s tableau@(Tableau tID tVs hs (Target [Left t@(Statement n (
        Exists evs inner
        ) _)])) = do
            inner's <- mapM (createStatement STTarget) $ conjuncts inner
            newTableau@(Tableau tID' tVs' hs' t') <- createTableau' True [] $ Target (Left <$> inner's)
            let newTableau' = Tableau tID' (tVs' ++ evs) hs' t'
--            ui' <- createStatement STTarget ui
            return (MoveDescription [n] [TargetIs [t] {-,Let [Suspended $ addDiamond <$> vs]-}] $
                        "Unlock existential target " ++ texSN n ++ ".",
                        s . addDiamondsInTableau evs $ Tableau tID tVs hs (Target  [Right [newTableau']]))
    onTableau _ _ _ = mzero



convertDiamondToBullet :: MoveType
convertDiamondToBullet = tableauwise onTableau where

    onTableau  :: [Statement] -> Surroundings -> Tableau -> RobotM (MoveDescription, Tableau)
    onTableau inheritedHs s (Tableau tN@(TableauName True tID) tVs hs t) = do
        -- find all diamonded variables owned by this tableau
        let diamonded = [v | v@(Variable _ _ _ VTDiamond _) <- tVs]

        guard . not $ null diamonded
        guard . not $ null hs

        let convert :: Variable -> Variable
            convert v@(Variable n id t VTDiamond ds)
                | v `elem` diamonded = Variable n id t VTBullet ds
            convert v = v

            tableau' = mapVariableInTableau convert $ Tableau (TableauName False tID) tVs hs t

        return (MoveDescription [] [AssumeNow hs] $
                   "Replacing diamonds with bullets in " ++ texTN tN ++ ".",
                s $ tableau')
    onTableau _ _ _ = mzero
