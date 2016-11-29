module Library (
    Library(..),
    Result(..),
    Solution(..),
    ExpansionTable(..),
    RewriteTable(..)
) where

import Types

data Library = Library [Result] [Solution] ExpansionTable RewriteTable                 deriving Show

data Result = Result {-description-} String {-premises-} [Formula] {-conclusion-} Formula
                                                                                       deriving Show

data Solution = Solution [Variable] [Formula] [Term] {-solution to existence problem-} deriving Show

type ExpansionTable = [(FormulaWithSlots, Formula)]

type RewriteTable = [(Term, [Variable], Term)]
