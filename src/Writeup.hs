{-# LANGUAGE FlexibleInstances #-}

module Writeup
  where


import Control.Applicative
--import Control.Arrow
----import Control.Monad.RWS hiding (msum)
--import Control.Monad.Logic hiding (msum)
--import Control.Monad.Trans.List
--import Control.Monad.Trans.State.Lazy
--import Control.Monad.Identity hiding (msum)
import Control.Monad
--import Data.Either
import Data.List
import Data.Maybe
--import Data.Map hiding (map, filter, null)
--import Data.Foldable (msum)
import Data.Char
import Data.Map (Map, (!))
import qualified Data.Map as Map

import Debug.Trace

import Printing
import Types
import TexBase
import Tex


----------------------------------------------------------------------------------------------------

class Writeup a where
    writeup :: PrintingData -> a -> String

----------------------------------------------------------------------------------------------------

commaList :: [String] -> String
commaList [] = error "commaList called with empty list"
commaList [s] = s
commaList ss = intercalate "," ss

andList :: [String] -> String
andList [] = "EMPTYANDLIST" -- error "andList called with empty list"
andList [s] = s
andList ss = intercalate ", " (init ss) ++ " and " ++ last ss

orList :: [String] -> String
orList [] = error "orList called with empty list"
orList [s] = s
orList ss = intercalate ", " (init ss) ++ " or " ++ last ss

instance Writeup Predicate where
    writeup pd p = tex pd p

instance Writeup Function where
    writeup pd f = tex pd f

writeupID :: ID -> String
writeupID n = replicate (n-1) '\''

instance Writeup Variable where
    writeup pd (Variable s id t hasBullet d) = tex pd . Variable s id t VTNormal $ Dependencies [] []

writeupIntro :: PrintingData -> Variable -> String
writeupIntro pd v@(Variable _ _ TPositiveRealNumber _ _) = writeup pd v ++ " > 0"
writeupIntro pd v = writeup pd v

writeupSequenceShort :: PrintingData -> Term -> String
writeupSequenceShort pd (VariableTerm (Variable "an" id _ _ _)) = "a_n" ++ writeupID id
writeupSequenceShort pd t = writeup pd t

writeupSequenceElement :: Variable -> String -> String
writeupSequenceElement (Variable "an" id _ _ _) s = "a_{" ++ s ++ "}" ++ writeupID id

instance Writeup Term where
    writeup pd (ApplyFn (Function "applyfnpointwise") [f,an]) = writeup pd f ++ "(" ++ writeupSequenceShort pd an ++ ")"
    writeup pd (ApplyFn (Function "kthterm") [VariableTerm an,k]) = writeupSequenceElement an (writeup pd k)

    writeup pd (VariableTerm v) = writeup pd v
    writeup pd (ApplyFn fn@(Function name) args) =  case Map.lookup name (termPatterns pd) of
        Just p -> instantiatePattern p $ writeup pd <$> args
        Nothing -> writeup pd fn ++ "(" ++ intercalate "," (writeup pd <$> args) ++ ")"


--TODO: generalise these to search through all conjuncts properly
--         and to handle multiple variables.
writeupST :: PrintingData -> [Variable] -> Formula -> String
writeupST pd [v] (And (AtomicFormula (Predicate "in") [VariableTerm v',t]:fs@(_:_)))
    | v == v' = math (writeup pd v ++ "\\in " ++ writeup pd t) ++ " s.t. " ++ writeup pd (And fs)
writeupST pd vs f = math (commaList $ writeupIntro pd <$> vs) ++ " s.t. " ++ writeup pd f

writeupSuchThat :: PrintingData -> [Variable] -> Formula -> String
writeupSuchThat pd [v] (And (AtomicFormula (Predicate "in") [VariableTerm v',t]:fs@(_:_)))
    | v == v' = math (writeup pd v ++ "\\in " ++ writeup pd t) ++ " such that " ++ writeup pd (And fs)
writeupSuchThat pd vs f = math (commaList $ writeupIntro pd <$> vs) ++ " such that " ++ writeup pd f


instance Writeup Formula where
    writeup pd (AtomicFormula (Predicate "tendsto") [an,b]) = math $ writeupSequenceShort pd an ++ "\\to " ++ writeup pd b

    writeup pd (AtomicFormula pred@(Predicate name) args) = case Map.lookup name (formulaPatterns pd) of
        Just p -> instantiatePattern p $ writeup pd <$> args
        Nothing -> math $ writeup pd pred ++ "(" ++ intercalate "," (writeup pd <$> args) ++ ")"

    writeup pd (Not f) = "it is not that case that " ++ writeup pd f
    writeup pd (And fs) = andList $ writeup pd <$> fs
    writeup pd (Or fs) = orList $ writeup pd <$> fs
    writeup pd (Forall vs f) = math $ "\\forall " ++ commaList (writeup pd <$> vs) ++ ".(" ++ textrm (writeup pd f) ++ ")"
    writeup pd (UniversalImplies _ [f@(AtomicFormula _ _)] f'@(AtomicFormula _ _)) =
        writeup pd f' ++ textrm " whenever " ++ writeup pd f
    writeup pd (UniversalImplies _ [f] f') = "if " ++ writeup pd f ++ ", then " ++ writeup pd f'
    writeup pd (UniversalImplies vs fs f') = math $ "\\forall " ++ intercalate ", " (writeup pd <$> vs) ++
                                               ".(" ++ textrm (writeup pd (And fs)) ++ "\\Rightarrow " ++ textrm (writeup pd f') ++ ")"
    writeup pd (Exists vs f) = "there exist " ++ writeupST pd vs f

instance Writeup VariableChoice where
    writeup pd (VariableChoice v t) = math $ writeup pd v ++ " = " ++ writeup pd t

instance Writeup Statement where
    writeup pd (Statement n f _) = writeup pd f


instance Writeup [Formula] where
    writeup pd fs = andList $ writeup pd <$> fs

instance Writeup [Statement] where
    writeup pd ss = andList $ writeup pd <$> ss

----------------------------------------------------------------------------------------------------

type Follows = Bool

data Clause = StubClause String
            | ProofDone                     -- we are done
            | TargetReminder [Statement]    -- we are trying to show X
            | TargetIs [Statement]          -- we would like to show X
            | TargetIsIE [Statement] [Statement]         -- we would like to show X, i.e. Y
            | Let [LetArgs]
            | Take [Variable]
            | Assertion [Statement]         -- X
            | WeMayTake [VariableChoice]            -- we may therefore take x = T
            | ThereforeSettingDone [VariableChoice] -- therefore, setting x = T, we are done
            | If [Statement] Statement --P and P' if Q
            | Whenever [Statement] Statement --P and P' whenever Q
            | Iff [Statement] [Statement]
            | AssumeNow [Statement]
            | ClearlyTheCaseDone  -- But this is clearly the case, so we are done

            | ExistVars [Variable] Clause
            | Since [Statement] Follows [Clause]
            | ByDefSince [Statement] Follows [Clause]
            | WeKnowThat [Clause]
            | But Clause  --may turn into an adverb

data LetArgs = BeSuchThat [Variable] [Statement]  -- let x and y be be s.t X
             | Suspended [Variable]                 -- let x be a constant to be chosen later
--             | Unconstrained Variable             -- let epsilon > 0

data Adverb = Then | So  | Also | AndA | IE | Therefore | Thus   deriving Eq

data Unit = Unit (Maybe Adverb) [Clause]

since :: [Statement] -> Clause -> Clause
since [] c = c
since ss c = Since ss False [c]

byDefSince :: [Statement] -> Clause -> Clause
byDefSince [] c = c
byDefSince ss c = ByDefSince ss False [c]

existVars :: [Variable] -> Clause -> Clause
existVars [] c = c
existVars vs c = ExistVars vs c

weKnowThat :: Clause -> Clause
weKnowThat c = WeKnowThat [c]

----------------------------------------------------------------------------------------------------


isNominal :: PrintingData -> Formula -> Bool
isNominal pd (AtomicFormula (Predicate name) _) = name `Map.member` nounPatterns pd
isNominal _  _ = False

isAdjectival :: PrintingData -> Formula -> Bool
isAdjectival pd (AtomicFormula (Predicate name) _) = name `Map.member` adjectivePatterns pd
isAdjectival _  _ = False

writeupNoun :: PrintingData -> Formula -> String
writeupNoun pd (AtomicFormula (Predicate name) (a:as)) =
    instantiatePattern (nounPatterns pd ! name) (writeup pd <$> as)

writeupAdjective :: PrintingData -> Formula -> String
writeupAdjective pd (AtomicFormula (Predicate name) (a:as)) =
    instantiatePattern (adjectivePatterns pd ! name) (writeup pd <$> as)

----------------------------------------------------------------------------------------------------

addAOrAn :: String -> String
addAOrAn s@(c:_)
    | c `elem` "aeiou" = "an " ++ s
    | otherwise = "a " ++ s

instance Writeup LetArgs where
    writeup pd (BeSuchThat [v] ss) =
      let fs = [f | Statement _ f _ <- ss]
          aboutVs = [f | f@(AtomicFormula _ (VariableTerm v':_)) <- fs, v' == v]
          ns = filter (isNominal pd) aboutVs
          as = filter (isAdjectival pd) aboutVs
          rests = fs \\ (ns ++ as)

       in "let " ++ math (writeupIntro pd v) ++ " be " ++ case (ns, as, rests) of
          ((n:n's), _, _) ->
            addAOrAn (concatMap ((++ " ") . writeupAdjective pd) as ++ writeupNoun pd n) ++
            (guard (not . null $ n's ++ rests) >> (" such that " ++ writeup pd (n's ++ rests)))

          _ -> "such that " ++ writeup pd fs

--    writeup pd (BeSuchThat [v] [Statement _ (AtomicFormula (Predicate "in") [v',t]) _]) =
--        "let " ++ math (writeupIntro v) ++ " be an element of " ++ math (writeup t)
    writeup pd (BeSuchThat vs ss) = "let " ++ andList (math . writeupIntro pd <$> vs) ++
                                         " be such that " ++ writeup pd ss
    writeup pd (Suspended [v]) = "let " ++ math (writeupIntro pd v)  ++ " be a constant to be chosen later"
    writeup pd (Suspended vs) = "let " ++ andList (math . writeupIntro pd <$> vs)  ++ " be constants to be chosen later"
--    writeup pd (Unconstrained v@(Variable _ _ TPositiveRealNumber _ _)) = "let " ++ math (writeupIntro v)
--    writeup pd (Unconstrained v@(Variable _ _ TPoint _ _)) = "let " ++ math (writeupIntro v) ++ " be a point"
--    writeup pd (Unconstrained v) = "let " ++ math (writeupIntro v) ++ " be a constant"

writeupShow :: PrintingData -> [Statement] -> String
writeupShow pd [Statement _ (Exists vs f) _] = "find " ++ writeupST pd vs f
writeupShow pd ss = "show that " ++ writeup pd ss

extractFormulae :: [Statement] -> Formula
extractFormulae [Statement _ f _] = f
extractFormulae ss = And [f | Statement _ f _ <- ss]

instance Writeup Clause where
    writeup pd (StubClause s) = textbf $ "[" ++ s ++ "]"
    writeup pd ProofDone = "we are done"
    writeup pd (TargetReminder ss) = "[we are trying to " ++ writeupShow pd ss ++ ".]"
    writeup pd (TargetIs ss) = "we would like to " ++ writeupShow pd ss
    writeup pd (TargetIsIE ss s's) = "we would like to show that " ++ writeup pd ss ++ ", i.e. that " ++ writeup pd s's
    writeup pd (Let as) = andList $ writeup pd <$> as
    writeup pd (Take [v@(Variable _ _ TPositiveRealNumber _ _)]) = "let " ++ math (writeupIntro pd v)
    writeup pd (Take vs) = "take " ++ andList (math . writeupIntro pd <$> vs)
    writeup pd (Assertion ss) = writeup pd ss
    writeup pd (WeMayTake vcs) = "we may therefore take " ++ andList (writeup pd <$> vcs)
    writeup pd (ThereforeSettingDone vcs) = "therefore, setting " ++ andList (writeup pd <$> vcs) ++ ", we are done"
    writeup pd (If as c) = writeup pd c ++ " if " ++ andList (writeup pd <$> as)
    writeup pd (Whenever as c) = writeup pd c ++ " whenever " ++ andList (writeup pd <$> as)
    writeup pd (Iff ss s's) = writeup pd ss ++ " if and only if " ++ writeup pd s's
    writeup pd (AssumeNow ss) = "assume now that " ++ writeup pd ss
    writeup pd (ExistVars [v] (Assertion ss)) =
        "there exists " ++ writeupSuchThat pd [v] (extractFormulae ss)
    writeup pd (ExistVars [v] c) =
        "there exists " ++ math (writeupIntro pd v) ++ " such that " ++ writeup pd c
    writeup pd (ExistVars vs c) =
        "there exist " ++ andList (math . writeupIntro pd <$> vs) ++ " such that " ++ writeup pd c
    writeup pd (Since ss False cs@[Assertion [Statement _ (AtomicFormula _ _) _]]) =
        "since " ++ writeup pd ss ++ ", we have that " ++ writeup pd cs
    writeup pd (Since ss f cs) = "since " ++ writeup pd ss ++ ", " ++ (guard f >> "it follows that ") ++ writeup pd cs
    writeup pd (ByDefSince ss False cs@[Assertion [Statement _ (AtomicFormula _ _) _]]) =
        "by definition, since " ++ writeup pd ss ++ ", we have that " ++ writeup pd cs
    writeup pd (ByDefSince ss f cs) = "by definition, since " ++ writeup pd ss ++ ", " ++ (guard f >> "it follows that ") ++ writeup pd cs
    writeup pd (WeKnowThat cs) = "we know " ++ andList (("that " ++) . writeup pd <$> cs)
    writeup pd (But c) = "but " ++ writeup pd c
    writeup pd ClearlyTheCaseDone = "but this is clearly the case, so we are done"

instance Writeup [Clause] where
    writeup pd cs = andList $ writeup pd <$> cs

instance Writeup Adverb where
    writeup _ Then = "then"
    writeup _ So = "so"
    writeup _ Also = "also"
    writeup _ AndA = "and"
    writeup _ IE = "that is,"
    writeup _ Therefore = "therefore"
    writeup _ Thus = "thus"

instance Writeup Unit where
    writeup pd (Unit (Just a) cs@(Since _ _ _:_))
        | a /= IE = writeup pd a ++ ", " ++ writeup pd cs
    writeup pd (Unit (Just a) cs) = writeup pd a ++ " " ++ writeup pd cs
    writeup pd (Unit Nothing cs) = writeup pd cs

asSentence :: String -> String
asSentence (c:cs) = (toUpper c:cs) ++ (guard (length cs >= 2 && last cs /= ']') >> ".")

----------------------------------------------------------------------------------------------------

--Sometimes The same statement will have different tags at different points in the proof, so
--  Also sometimes variables will have gained/lost a diamond/circle
--  So we need to compare the statement names, not the formulae

(===) :: Statement -> Statement -> Bool
Statement n _ _ === Statement n' _ _ = n == n'

(=:=) :: [Statement] -> [Statement] -> Bool
ss =:= s's = and $ zipWith (===) ss s's

nameElem :: Statement -> [Statement] -> Bool
nameElem s (s':s's)
    | s === s' = True
    | otherwise = s `nameElem` s's
nameElem s [] = False

nameNotElem :: Statement -> [Statement] -> Bool
nameNotElem s = not . nameElem s

----------------------------------------------------------------------------------------------------

--code to fuse together clauses were possible; e.g.
--   since P, Q. since P, R.
-- is changed into
--   since P, Q and R


fuse :: [Clause] -> [Clause]
fuse (c:cs@(c':c's)) = case fusePair c c' of
    Just f -> fuse $ f:c's
    Nothing -> c:fuse cs
fuse (c:[]) = [c]
fuse [] = []

fusePair :: Clause -> Clause -> Maybe Clause
fusePair (Since ss False cs) (Since s's False c's)
    | ss =:= s's = Just . Since ss False . fuse $ cs ++ c's
fusePair (Let as) (Let a's) = Just . Let $ as ++ a's
fusePair (WeKnowThat as) (WeKnowThat a's) = Just . WeKnowThat $ as ++ a's
fusePair t@(TargetIs ss) (TargetIs s's)
    | ss == s's = Just t
fusePair t@(TargetIsIE ss s's) (TargetIs s''s)
    | s's == s''s = Just t
fusePair _ _ = Nothing

----------------------------------------------------------------------------------------------------

--eliminate references to facts just introduced and introduce corresponding rhetorical structure:
-- E.g.
--   P. since P and Q, R.
-- is changed into
--   P. since Q, it follows that R.

--factsDeduced: the facts deduced in a particular step
factsDeduced :: Clause -> [Statement]
factsDeduced (StubClause s) = []
factsDeduced ProofDone = []
factsDeduced (TargetReminder ss) = []
factsDeduced (TargetIs ss) = []
factsDeduced (TargetIsIE _ _) = []
factsDeduced (Let as) = []
factsDeduced (Take _) = []
factsDeduced (Assertion ss) = ss
factsDeduced (WeMayTake cs) = []
factsDeduced (ThereforeSettingDone cs) = []
factsDeduced (If as c) = []
factsDeduced (Whenever as c) = []
factsDeduced (Iff ss s's) = ss ++ s's
factsDeduced (AssumeNow ss) = ss
factsDeduced (ExistVars vs c) = [] --factsDeduced c
factsDeduced (Since ss f cs) = concatMap factsDeduced cs
factsDeduced (ByDefSince ss f cs) = concatMap factsDeduced cs
factsDeduced (WeKnowThat cs) = concatMap factsDeduced cs
factsDeduced (But c) = factsDeduced c
factsDeduced ClearlyTheCaseDone = []

--factsDeclared: the facts declared by 'let's, etc. in a particular step
factsDeclared :: Clause -> [Statement]
factsDeclared (Let as) = concat [ss | BeSuchThat _ ss <- as]
factsDeclared _ = []

isAtomicStatement :: Statement -> Bool
isAtomicStatement (Statement _ f _) = isAtomic f

--atomicFactsPresented :: Clause -> [Statement]
--atomicFactsPresented = const [] --filter isAtomicStatement . factsDeduced

--TODO tidy
eliminate :: [Clause] -> [Unit]
eliminate cs = zipWith4 convert factsDeducedInPrevClause factsDeclaredInPrevClause twoBack cs where
    factsDeducedInPrevClause = []:(factsDeduced <$> cs)
    factsDeclaredInPrevClause = []:(factsDeclared <$> cs)
    twoBack = []:[]:(factsDeduced <$> cs)
--    allAtomicFactsPresented    = [concatMap atomicFactsPresented prev | (c, prev) <- zip cs (inits cs)]

--convert: factsDeducedInPrevClause -> factsDeclaredInPrevClause -> twoBack -> ThisClause -> Unit
convert :: [Statement] -> [Statement] -> [Statement] -> Clause -> Unit
convert fs ls as (Since ss _ cs)
    | all (`nameElem` (fs ++ ls ++ as)) ss && any (`nameElem` (fs ++ ls)) ss = Unit (Just Then) $ cs
    | any (`nameElem` fs) ss = Unit (Just Therefore) [Since (filter (`nameNotElem` (fs ++ ls ++ as)) ss) False cs]
    | any (`nameElem` ls) ss = Unit (Just Then)      [Since (filter (`nameNotElem` (ls ++ as)) ss) False cs]
    | all (`nameElem` as) ss = Unit (Just AndA) $ cs
    | any (`nameElem` as) ss = Unit (Just AndA) [Since (filter (`nameNotElem` as) ss) False cs]
convert fs ls as (ByDefSince ss _ cs)
    | all (`nameElem` (ls ++ as)) ss && any (`nameElem` ls) ss = Unit (Just Then) $ cs
    | all (`nameElem` (fs ++ ls ++ as)) ss && any (`nameElem` (fs ++ ls)) ss = Unit (Just IE) $ cs
    | any (`nameElem` fs) ss = Unit (Just Therefore) [ByDefSince (filter (`nameNotElem` (fs ++ ls ++ as)) ss) False cs]
    | any (`nameElem` ls) ss = Unit (Just Then)      [ByDefSince (filter (`nameNotElem` (ls ++ as)) ss) False cs]
    | all (`nameElem` as) ss = Unit (Just AndA) $ cs
    | any (`nameElem` as) ss = Unit (Just AndA) [ByDefSince (filter (`nameNotElem` as) ss) False cs]
convert fs ls as c = Unit Nothing [c]

----------------------------------------------------------------------------------------------------

compress :: [Unit] -> [Unit]
compress (Unit ma cs:Unit (Just AndA) c's:u's) = compress (Unit ma (cs ++ c's):u's)
compress [Unit ma cs, Unit Nothing [ProofDone]] = [Unit ma $ cs ++ [ProofDone]]
compress [Unit Nothing [TargetIs ss], Unit Nothing [ClearlyTheCaseDone]] = [Unit (Just Thus) [Assertion ss, ProofDone]]
compress (u:us)= u:compress us
compress us = us
