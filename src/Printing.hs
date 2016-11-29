module Printing (
    Pattern, instantiatePattern,
    PrintingData(..)
) where

import Data.Map (Map, (!))
import qualified Data.Map as Map

----------------------------------------------------------------------------------------------------

type Pattern = String

instantiatePattern :: Pattern -> [String] -> String
instantiatePattern ('%':cs) (s:ss) = s ++ instantiatePattern cs ss
instantiatePattern (c:cs) ss = c : instantiatePattern cs ss
instantiatePattern [] [] = ""

data PrintingData = PrintingData {
    termPatterns :: Map String Pattern,
    formulaPatterns :: Map String Pattern,
    nounPatterns :: Map String Pattern,
    adjectivePatterns :: Map String Pattern
  }                                                                                    deriving Show

