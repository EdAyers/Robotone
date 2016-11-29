{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Tex (
    Tex, tex,
    texTuple,
    texList, texOrList,
    texSN, texSNs, texTN,
    texTableauBolding
) where


import Prelude hiding (repeat)
import Control.Applicative
import Data.Functor.Identity
import Control.Monad
import Control.Monad.Writer.Lazy (Writer, tell, runWriter)
import Data.Monoid
import Data.List
import Data.Set (member)
import Data.Map (Map, (!))
import qualified Data.Map as Map

import Printing
import TexBase
import Types

----------------------------------------------------------------------------------------------------

class Tex a where
    tex :: PrintingData -> a -> String

----------------------------------------------------------------------------------------------------


instance Tex Function where
    tex pd (Function "min") = "\\min"
    tex pd (Function s) = textit s
instance Tex Predicate where
    tex pd (Predicate s) = textit s

texID :: ID -> String
texID n = replicate (n-1) '\''

texVariableNameID :: String -> ID -> String
texVariableNameID "an" id = "(a_n" ++ texID id ++ ")"
texVariableNameID s id
    | s `member` texableGreekLetters = "\\" ++ s ++ texID id
    | otherwise = s ++ texID id

texSequenceShort :: PrintingData -> Term -> String
texSequenceShort pd (VariableTerm (Variable "an" id _ _ _)) = "a_n" ++ texID id
texSequenceShort pd t = tex pd t

texSequenceElement :: Variable -> String -> String
texSequenceElement (Variable "an" id _ _ _) s = "a_{" ++ s ++ "}" ++ texID id

instance Tex Dependencies where
    tex pd (Dependencies [] []) = ""
    tex pd (Dependencies ds is) = "[" ++ intercalate "," (map (tex pd) ds ++ (overline . tex pd <$> is)) ++ "]"

instance Tex VariableType where
    tex pd VTNormal = ""
    tex pd VTDiamond = {--"^\\bullet " TEMP-} "^\\blacklozenge "
    tex pd VTBullet = "^\\bullet "

instance Tex Variable where
    tex pd (Variable s id _ vtype d) =
        texVariableNameID s id ++ tex pd vtype ++ tex pd d

texList :: [String] -> String
texList [] = error "texList called with empty list"
texList [s] = s
texList ss = intercalate ", " (init ss) ++ " and " ++ last ss

texOrList :: [String] -> String
texOrList [] = error "texOrList called with empty list"
texOrList [s] = s
texOrList ss = intercalate ", " (init ss) ++ " or " ++ last ss

--texVariableList :: [Variable] -> String
--texVariableList [] = error "texVariableList called with empty variable list"
--texVariableList [v] = "$" ++ tex v ++ "$"
--texVariableList vs = intercalate "," (math . tex <$> init vs) ++ " and " ++ math (tex $ last vs)
--    where math s = "$" ++ s ++ "$"

instance Tex Term where
    tex pd (ApplyFn (Function "applyfnpointwise") [f,an]) = tex pd f ++ "(" ++ texSequenceShort pd an ++ ")"
    tex pd (ApplyFn (Function "kthterm") [VariableTerm an,k]) = texSequenceElement an (tex pd k)

    tex pd (VariableTerm v) = tex pd v
    tex pd (ApplyFn fn@(Function name) args) =  case Map.lookup name (termPatterns pd) of
        Just p -> instantiatePattern p $ tex pd <$> args
        Nothing -> tex pd fn ++ "(" ++ intercalate "," (tex pd <$> args) ++ ")"

instance Tex Formula where
    tex pd (AtomicFormula (Predicate "tendsto") [an,b]) = texSequenceShort pd an ++ "\\to " ++ tex pd b

    tex pd (AtomicFormula pred@(Predicate name) args) =  case Map.lookup name (formulaPatterns pd) of
        Just p -> textrm . instantiatePattern p $ tex pd <$> args
        Nothing -> tex pd pred ++ "(" ++ intercalate "," (tex pd <$> args) ++ ")"

    tex pd (Not f) = "\\neg " ++ tex pd f
    tex pd (And fs) = intercalate "\\wedge " $ tex pd <$> fs
    tex pd (Or fs) = intercalate "\\vee " $ tex pd <$> fs
    tex pd (Forall vs f) = "\\forall " ++ intercalate ", " (tex pd <$> vs) ++ ".(" ++ tex pd f ++ ")"
--    tex pd (UniversalImplies _ [f@(AtomicFormula _ _)] f'@(AtomicFormula _ _)) =
--        tex f' ++ textrm " whenever " ++ tex f
--    tex pd (UniversalImplies _ [f] f') = textrm "if " ++ tex f ++ textrm ", then " ++ tex f'
    tex pd (UniversalImplies vs fs f') = "\\forall " ++ intercalate ", " (tex pd <$> vs) ++
                                           ".(" ++ tex pd (And fs) ++ "\\Rightarrow " ++ tex pd f' ++ ")"
--    tex pd (Exists [v] f) = textrm "there is a " ++ tex v ++ textrm " s.t. " ++ tex f
    tex pd (Exists vs f) = "\\exists " ++ intercalate ", " (tex pd <$> vs) ++ ".(" ++ tex pd f ++ ")"


texST :: StatementType -> String
texST STHypothesis = "H"
texST STTarget = "T"

texSN :: StatementName -> String
texSN (StatementName t id) = texST t ++ show id

texSNs :: [StatementName] -> String
texSNs [n] = texSN n
texSNs ns = "(" ++ intercalate "," (texSN <$> ns) ++ ")"

texTuple :: Tex a => PrintingData -> [a] -> String
texTuple pd [a] = tex pd a
texTuple pd as = "(" ++ intercalate "," (tex pd <$> as) ++ ")"

instance Tex Tag where
    tex pd Vulnerable = "Vuln."
    tex pd Deleted =  error "A 'Deleted' tag should never be printed."
    tex pd (MovedDownFrom n) =  "From " ++ tex pd n ++ "."
    tex pd (UsedForwardsWith ns) = "Used with " ++ texSNs ns ++ "."
    tex pd (UsedBackwardsWith ns) = "Used with " ++ texSNs ns ++ "."
    tex pd (CannotSubstitute ts) = "Cannot subst. " ++ intercalate "," (texTuple pd <$> ts)

instance Tex Statement where
    tex pd s@(Statement n f ts)
        | Deleted `elem` ts = grey (texStatementCore pd s) {--TEMP-} ++ "&" ++ texTagsGrey pd ts
        | otherwise = texStatementCore pd s {--TEMP-} ++ "&" ++ texTags pd ts


texStatementBold :: PrintingData -> Statement -> String
texStatementBold pd s@(Statement n f ts)
        | Deleted `elem` ts = grey (textbf . boldmath $ texStatementCore pd s) {--TEMP-} ++ "&" ++ (textbf . boldmath $ texTagsGrey pd ts)
        | otherwise = (textbf . boldmath $ texStatementCore pd s) {--TEMP-} ++ "&" ++ (textbf . boldmath $ texTags pd ts)

texStatementCore :: PrintingData -> Statement -> String
texStatementCore pd (Statement n f ts) = texSN n ++ ".\\ " ++ math (tex pd f)

texTags :: PrintingData -> [Tag] -> String
texTags pd [] = ""
texTags pd ts = "[" ++ intercalate "; " (tex pd <$> filter (/= Deleted) ts) ++ "]"

texTagsGrey :: PrintingData -> [Tag] -> String
texTagsGrey pd [] = ""
texTagsGrey pd ts = grey ("[" ++ intercalate "; " (tex pd <$> filter (/= Deleted) ts) ++ "]")

instance Tex TableauName where
    tex pd (TableauName hasDagger id) = "L" ++ show id ++ (guard hasDagger >> "$^\\blacklozenge$")

texTN :: TableauName -> String
texTN (TableauName hasDagger id) = "L" ++ show id ++ (guard hasDagger >> "$^\\blacklozenge$")

instance Tex Tableau where
    tex pd = texTableauBolding pd []

texTableauBolding :: PrintingData -> [StatementName] -> Tableau -> String
texTableauBolding pd ns (Tableau (TableauName hasDagger id) vs ss t) = unlines
    ["\\begin{tikzpicture}[baseline=(main.base)]%",
     "\\node[tableau] (main) {%",
{--TEMP-}     intercalate "\\hspace{1.5mm}" (math . tex pd <$> vs) ++ "\\\\\n",
     "\\begin{tabular}{ll}%",
     intercalate "\\\\\n"
         [if n `elem` ns then texStatementBold pd s else tex pd s | s@(Statement n _ _) <- ss],
     "\\Bstrut\\\\\\hline\\Tstrut",
     texTargetBolding pd ns t,
     "\\end{tabular}%",
     "};%",
     "\\node[tableaulabel] at (main.north west) [xshift=4mm, yshift=-5.5mm] {L" ++ show id  ++ (guard hasDagger >> "$^\\blacklozenge$") ++ "};",
--     "\\node[tableaulabel] at (main.north west) [xshift=4mm, yshift=-5.5mm] {L" ++ show id  ++ {-TEMP (guard hasDagger >> "$^\\blacklozenge$") ++ -}"};",
     "\\end{tikzpicture}%"]
texTableauBolding _  _ (Done (TableauName hasDagger id)) =  unlines
    ["\\begin{tikzpicture}%",
     "\\node[tableau] (main) {%",
     "\\ \\ \\,Done",
     "};%",
     "\\node[tableaulabel] at (main.north west) [xshift=4mm, yshift=-5.5mm] {L" ++ show id ++ (guard hasDagger >> "$^\\blacklozenge$") ++ "};",
--     "\\node[tableaulabel] at (main.north west) [xshift=4mm, yshift=-5.5mm] {L" ++ show id ++ {-TEMP (guard hasDagger >> "$^\\blacklozenge$") ++ -}"};",
     "\\end{tikzpicture}%"]

--     "\\node[tableaulabel] at (main.north west) [xshift=4mm, yshift=-5.5mm] {L" ++ show id ++ "};",

instance Tex Target where  --output goes inside an array env.
--    tex (Target ps) = intercalate "\\\\\n" [either tex tex p | p <- ps]
--    tex Contradiction = "Contradiction"
    tex pd = texTargetBolding pd []

texTargetBolding :: PrintingData -> [StatementName] -> Target -> String
texTargetBolding pd ns (Target ps) = intercalate "\\\\\n" $ either f (intercalate "\\hspace{2mm}$\\vee$" . map (texTableauBolding pd ns)) <$> ps where
    f s@(Statement n _ _) | n `elem` ns = texStatementBold pd s
                          | otherwise   = tex pd s
texTargetBolding _  ns Contradiction = "Contradiction"

instance Tex VariableChoice where
    tex pd (VariableChoice v t) = math $ tex pd v ++ " = " ++ tex pd t
