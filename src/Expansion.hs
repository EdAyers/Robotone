{-# LANGUAGE NoMonomorphismRestriction #-}
module Expansion (
    primaryExpansion, allExpansions, isUnexpandable,
    rewriteTerm, rewriteFormula
) where

import Prelude hiding ((/))
import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Parser

import Library
import RobotM
import Types
import Match
import Move

----------------------------------------------------------------------------------------------------

--TODO: consider moving primaryExpansion', isUnexpandable into the RobotM monad

primaryExpansion' :: Formula -> RobotM (Maybe (Matching, Formula))
primaryExpansion' f = do
    et <- askLibraryExpansionTable
    return . listToMaybe $ do
        (pattern, expansion) <- et
        matching <- maybeToList $ match pattern f
        return (matching, expansion)
--    return $ transform matching expansion

isUnexpandable :: Formula -> RobotM Bool
isUnexpandable f = do
    et <- askLibraryExpansionTable
    pe <- primaryExpansion' f
    return $ isNothing pe

primaryExpansion :: Formula -> RobotM Formula
primaryExpansion f = do
    et <- askLibraryExpansionTable
    rt <- askLibraryRewriteTable
    pe <- primaryExpansion' f
    (matching, expansion) <- oneOf $ maybeToList pe
    expansion' <- renameFormula expansion
    --rewriteFormulaIfPossible <$> renameFormula f'
    rewriteFormulaIfPossible $ transform matching expansion'

allExpansions :: Formula -> RobotM Formula
allExpansions = primaryExpansion

----------------------------------------------------------------------------------------------------

--NB: this term rewriting code does not use renameFormula  -- so DO NOT ever put quantifiers on RHS
--      of the rewrite trable.
--  (This is only relevant if we introduce sets, etc., so that formulae can be inside terms.)

rewriteTerm :: Term -> RobotM (Maybe Term)
rewriteTerm t = do
    rt <- askLibraryRewriteTable
    return . listToMaybe $ do
        (pattern, vs, rewriteTo) <- rt
        matching <- maybeToList $ matchTerm pattern vs t
        return $ transformTerm matching rewriteTo

rewriteTermIfPossible :: Term -> RobotM Term
rewriteTermIfPossible t = do
    rewritten <- rewriteTerm t
    return . fromMaybe t $ rewritten

rewriteFormulaIfPossible :: Formula -> RobotM Formula
rewriteFormulaIfPossible = mapTermInFormulaM rewriteTermIfPossible

rewriteFormula :: Formula -> RobotM (Maybe Formula)
rewriteFormula f = do f' <- mapTermInFormulaM rewriteTermIfPossible f
                      return $ if f == f' then Nothing else Just f'

----------------------------------------------------------------------------------------------------

