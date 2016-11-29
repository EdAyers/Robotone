module Parser (
    Parser.parse,
    variable,
    term,
    formula
) where


import Control.Applicative hiding (many, (<|>))
import qualified Data.Map as Map
import Data.Map (Map, (!))

--import Text.Parsec.Text.Lazy
import Text.Parsec.String
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim
import Text.Parsec.Error

import Types


----------------------------------------------------------------------------------------------------

parse :: Parser a -> String -> a
parse p = either (error . show) id . Text.Parsec.Prim.parse p ""

tryInTurn :: [Parser a] -> Parser a
tryInTurn = foldl1 (<|>) . map try

----------------------------------------------------------------------------------------------------

bracketed :: Parser a -> Parser a
bracketed p = string "(" *> spaces *> p <* spaces <* string ")"

punct :: String -> Parser String
punct s = spaces *> string s <* spaces

spaces1 = many1 space

----------------------------------------------------------------------------------------------------

conventionalTypes = Map.fromList [
    ("a", TPoint),
    ("b", TPoint),
    ("f", TFunction),
    ("g", TFunction),
    ("h", TFunction),
    ("n", TNaturalNumber),
    ("x", TPoint),
    ("y", TPoint),
    ("z", TPoint),
    ("u", TPoint),
    ("v", TPoint),
    ("w", TPoint),
    ("p", TPoint),
    ("q", TPoint),
    ("r", TPoint),
    ("s", TPoint),
    ("t", TPoint),
    ("A", TSet),
    ("B", TSet),
    ("C", TSet),
    ("D", TSet),
    ("F", TSet),
    ("H", TGroup),
    ("K", TGroup),
    ("N", TNaturalNumber),
    ("U", TSet),
    ("V", TSet),
    ("X", TSet),
    ("alpha", TPositiveRealNumber),
    ("beta", TPositiveRealNumber),
    ("gamma", TPositiveRealNumber),
    ("delta", TPositiveRealNumber),
    ("epsilon", TPositiveRealNumber),
    ("eta", TPositiveRealNumber),
    ("theta", TPositiveRealNumber),
    ("an", TSequence)
  ]

----------------------------------------------------------------------------------------------------

function :: Parser Function
function = Function <$> many1 alphaNum

predicate :: Parser Predicate
predicate = Predicate <$> many1 alphaNum

variable :: Parser Variable
variable = do
    n <- many1 letter
    ps <- many $ char '\''
    let t = Map.findWithDefault (error $ "Variable " ++ n ++ " does not have a conventional type.") n conventionalTypes
    return $ Variable n (length ps + 1) t VTNormal (Dependencies [] [])

term :: Parser Term
term = tryInTurn [
    ApplyFn <$> function <*> bracketed (sepBy term (try $ punct ",")),
    VariableTerm <$> variable
  ]


--rule_exp :: Parser RuleExp
--rule_exp = foldl (flip ($)) <$> rule_exp''
--                            <*> many (try_in_turn modifiers) <?> "Semantic expression"
--
--modifiers :: [Parser (RuleExp -> RuleExp)]
--modifiers  =
--   [flip Apply     <$> (whites *> bracketed rule_exp),
--    flip DRSMerge  <$> space_then_oplus_exp,
--    flip PluralSum <$> (punct "&" *> rule_exp)]
--
--space_then_oplus_exp :: Parser RuleExp
--space_then_oplus_exp = whites *> (string "⊕" <|> string "++") *> whites *> rule_exp

--TODO: parse negated formulae

formula :: Parser Formula --a conjunction of formula''s
formula = do
    ps <- sepBy1 formula' (try $ punct "|")
    case ps of
        [p] -> return p
        _ -> return $ Or ps

formula' :: Parser Formula --a conjunction of formula''s
formula' = do
    ps <- sepBy1 formula'' (try $ punct "&")
    case ps of
        [p] -> return p
        _ -> return $ And ps

formula'' :: Parser Formula
formula'' = tryInTurn [
    bracketed formula,
    Not <$> (string "¬" *> formula''),
    forall_,
    univCond,
    exists,
    AtomicFormula <$> predicate <*> bracketed (sepBy term (try $ punct ","))
  ]


forall_ :: Parser Formula
forall_ = Forall <$> (string "forall " *> spaces *> sepBy variable spaces1)
                 <*> (punct ".(" *> formula <* spaces <* string ")")

univCond :: Parser Formula
univCond = UniversalImplies <$> (string "forall " *> spaces *> sepBy variable spaces1)
                            <*> (punct ".(" *> sepBy1 formula'' (try $ punct "&"))
                            <*> (punct "=>" *> formula <* spaces <* string ")")


exists :: Parser Formula
exists = Exists <$> (string "exists " *> spaces *> sepBy variable spaces1)
                <*> (punct ".(" *> formula <* spaces <* string ")")

testF = "forall x.(in(x, intersect(A, B)) => exists delta.(forall y.(lessthan(d(x, y), delta) => in(y, intersect(A, B)))))"
testF2 = "forall y.(lessthan(d(x, y), delta) => in(y, intersect(A, B)))"
testF3 = "exists delta.(in(y, intersect(A, B)) & lessthan(d(x, y), delta))"
pu = Parser.parse univCond
pe = Parser.parse exists

