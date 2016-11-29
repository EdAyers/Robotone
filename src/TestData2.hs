module TestData2 (
    problems, library, printingData
) where

import Prelude hiding ((/))

import Control.Arrow
import Control.Applicative
import qualified Data.Map as Map
import Data.Map (Map)

import Types
import Expansion
import TexBase
import Parser
import Tex
import RobotM
import Library
import Writeup
import Printing

union3OpenSets = Problem
    "If $A$, $B$,and $C$ are open sets, then $A \\cup (B \\cup C)$ is also open." --"The union of three open sets is open."
   ["open(A)",
    "open(B)",
    "open(C)"]
    "open(union(A,union(B,C)))"

intersection3OpenSets = Problem
    "If $A$, $B$,and $C$ are open sets, then $A \\cap (B \\cap C)$ is also open." --"The intersection of three open sets is open."
   ["open(A)",
    "open(B)",
    "open(C)"]
    "open(intersect(A,intersect(B,C)))"

unionOpenSets = Problem
    "If $A$ and $B$ are open sets, then $A \\cup B$ is also open." --"The union of two open sets is open."
   ["open(A)",
    "open(B)"]
    "open(union(A,B))"

intersectionOpenSets = Problem
    "If $A$ and $B$ are open sets, then $A \\cap B$ is also open." --"The intersection of two open sets is open."
   ["open(A)",
    "open(B)"]
    "open(intersect(A,B))"

unionClosedSets = Problem
    "If $A$ and $B$ are closed sets, then $A \\cup B$ is also closed." --"The union of two closed sets is closed."
   ["closed(A)",
    "closed(B)"]
    "closed(union(A,B))"

intersectionClosedSets = Problem
    "If $A$ and $B$ are closed sets, then $A \\cap B$ is also closed." --"The intersection of two closed sets is closed."
   ["closed(A)",
    "closed(B)"]
    "closed(intersect(A,B))"

continuousPreimageClosed = Problem
    "The pre-image of a closed set $U$ under a continuous function $f$ is closed."
   ["continuous(f)",
    "closed(U)"]
    "closed(preimage(f,U))"

continuousPreimageOpen = Problem
    "The pre-image of an open set $U$ under a continuous function $f$ is open."
   ["continuous(f)",
    "open(U)"]
    "open(preimage(f,U))"

compositionContinuousFunctions = Problem
    "If $f$ and $g$ are continuous functions, then $g \\circ f$ is continuous." --"A composition of continuous functions is continuous."
   ["continuous(f)",
    "continuous(g)"]
    "continuous(compose(g,f))"

continuousFunctionsPreserveLimits = Problem
    "If $f$ is a continuous function and $(a_n) \\to a$, then $(f(a_n)) \\to f(a)$"-- "A continuous function preserves limits."
   ["continuous(f)",
    "tendsto(an,a)"]
    "tendsto(applyfnpointwise(f,an),applyfn(f,a))"

closedSubsetCompleteIsComplete = Problem
    "A closed subset $A$ of a complete metric space $X$ is complete."
   ["completespace(X)",
    "closedin(A,X)"]
    "complete(A)"

ffminusoneAsubsetA = Problem "$f(f^{-1}(A))\\subset A$"  [] "subsetof(image(f,preimage(f,A)),A)"

asubsetfminusonefA = Problem "$A \\subset f^{-1}(f(A))$" [] "subsetof(A, preimage(f,image(f,A)))"


iffInjectionThenfAcapfBsubsetfAcapB = Problem
    "If $f$ is an injection then $f(A)\\cap f(B)\\subset f(A\\cap B)$"
        ["injection(f)"]
        "subsetof(intersect(image(f,A),image(f,B)),image(f,intersect(A,B)))"

problems = [union3OpenSets,
            intersection3OpenSets,
            unionOpenSets,
            unionClosedSets,
            intersectionClosedSets,
            continuousPreimageClosed]
            
problems' = [intersectionOpenSets,
            continuousPreimageOpen,
            compositionContinuousFunctions,
            continuousFunctionsPreserveLimits,
            closedSubsetCompleteIsComplete,
            ffminusoneAsubsetA, asubsetfminusonefA,
            iffInjectionThenfAcapfBsubsetfAcapB
            ]
----------------------------------------------------------------------------------------------------


expansionTableSource :: [(String, String)]
expansionTableSource = [
    ("sequencein(an,intersect(A,B))", "sequencein(an,A) & sequencein(an,B)"),
    ("in(x,intersect(A,B))", "in(x,A) & in(x,B)"),
    ("in(x,union(A,B))", "in(x,A) | in(x,B)"),
    ("subsetof(A,intersect(B,C))","subsetof(A,B) & subsetof(A,C)"),
    ("subsetof(A,B)", "forall x.(in(x,A) => in(x,B))"),
    ("in(x,preimage(f,U))", "in(applyfn(f,x),U)"),
    ("sequencein(x,preimage(f,U))", "sequencein(applyfnpointwise(f,x),U)"), --NEW
    ("in(x,image(f,A))", "exists y.(in(y,A) & equals(applyfn(f,y),x))"),
    ("in(x,complement(A))", "notin(x,A)"),
    ("notin(x,A)","¬in(x,A)"),
    ("injection(f)", "forall x y z.(equals(applyfn(f,x),z) & equals(applyfn(f,y),z) => equals(x,y))"),
    ("sequencein(an,A)", "forall n.(in(kthterm(an,n),A))"),
    ("open(A)", "forall x.(in(x, A) => exists delta.(forall y.(lessthan(d(x, y), delta) => in(y, A))))"),
    ("continuous(f)", "forall x epsilon.(exists delta.(forall y.(lessthan(d(x, y), delta) => lessthan(d(applyfn(f,x), applyfn(f,y)), epsilon))))"),
    ("tendsto(an,a)", "forall epsilon.(exists N.(forall n.(atleast(n,N) => lessthan(d(a,kthterm(an,n)),epsilon))))"),
    ("completespace(X)", "forall an.(cauchy(an) => converges(an))"),
    ("complete(A)", "forall an.(cauchy(an) & sequencein(an,A) => convergesin(an,A))"),
    ("converges(an)", "exists a.(tendsto(an,a))"),
    ("convergesin(an,A)", "exists a.(in(a,A) & tendsto(an,a))"),
    ("closed(A)", "forall an a.(sequencein(an,A) & tendsto(an,a) => in(a,A))"),
    ("denseon(A,B)", "forall x epsilon.(in(x,B) => exists y.(in(y,A) & lessthan(d(x,y), epsilon)))"),
    ("cauchy(an)", "forall epsilon.(exists N.(forall m n.(atleast(m,N) & atleast(n,N) => lessthan(d(kthterm(an,m),kthterm(an,n)),epsilon))))"),
    ("subgroup(H)", "(forall x y.(in(x,H) & in(y,H) => in(product(x,y),H))) & in(e(),H) & (forall x.(in(x,H) => in(inverse(x),H)))")
  ]

expansionTable :: [(FormulaWithSlots, Formula)]
expansionTable = [(f / allVariablesInFormula f, f') |
                  (f, f') <- (parse formula *** parse formula) <$> expansionTableSource]


--NB: the term rewriting code does not use renameFormula  -- so DO NOT ever put quantifiers on RHS
--     of the rewrite table.
--  (This is only relevant if we introduce sets, etc., so that formulae can be inside terms.)

rewriteTableSource = [
    ("applyfn(compose(f,g),x)", "applyfn(f,applyfn(g,x))"),
    ("kthterm(applyfnpointwise(f,an),n)", "applyfn(f,kthterm(an,n))")
  ]


rewriteTable :: [(Term, [Variable], Term)]
rewriteTable = [(t, allVariablesInTerm t, t') |
                  (t, t') <- (parse term *** parse term) <$> rewriteTableSource ]

----------------------------------------------------------------------------------------------------


termPatterns' :: Map String Pattern
termPatterns' = Map.fromList [
    ("intersect", "%\\cap %"),
    ("union", "%\\cup %"),
    ("compose", "%\\circ %"),
    ("applyfn", "%(%)"),
    ("image", "%(%)"),
    ("preimage", "%^{-1}(%)"),
    ("complement", "%^c"),
    ("product", "%%"),
    ("inverse", "%^{-1}"),
    ("e", "e"),
    ("ball", "B_{%}(%)")
  ]

formulaPatterns' :: Map String Pattern
formulaPatterns' = Map.fromList [
    ("in", "$%\\in %$"),
    ("notin", "$%\\notin %$"),
    ("subsetof", "$%\\subset %$"),
    ("equals", "$% = %$"),
    ("lessthan", "$% < %$"),
    ("atleast", "$%\\geqslant %$"),
    ("atmost", "$%\\leqslant %$"),
    ("open", "$%$ is open"),
    ("closed", "$%$ is closed"),
    ("complete", "$%$ is a complete space"),
    ("completespace", "$%$ is complete"),
    ("closedin", "$%$ is closed in $%$"),
    ("sequencein", "$%$ is a sequence in $%$"),
    ("injection", "$%$ is an injection"),
    ("continuous", "$%$ is continuous"),
    ("cauchy", "$%$ is Cauchy"),
    ("converges", "$%$ converges"),
    ("convergesin", "$%$ converges in $%$"),
    ("mapsto", "$%:%\\mapsto %$"),
    ("subgroup", "$%$ is a subgroup")
  ]

nounPatterns' :: Map String Pattern
nounPatterns' = Map.fromList [
    ("in", "element of $%$"),
    ("subsetof", "subset of $%$"),
    ("sequencein", "sequence in $%$"),
    ("injection", "injection")
  ]

adjectivePatterns' :: Map String Pattern
adjectivePatterns' = Map.fromList [
    ("open", "open"),
    ("closed", "closed"),
    ("complete", "complete"),
    ("continuous", "continuous"),
    ("cauchy", "Cauchy")
  ]

printingData = PrintingData termPatterns' formulaPatterns' nounPatterns' adjectivePatterns'

library = Library [
    Result "transitivity" [
        parse formula "lessthan(alpha,beta)",
        parse formula "atmost(beta,gamma)"]
        (parse formula "lessthan(alpha,gamma)"),
    Result "" [
        parse formula "open(A)",
        parse formula "open(B)"]
        (parse formula "open(union(A,B))"),
    Result "" [
        parse formula "open(A)",
        parse formula "open(B)"]
        (parse formula "open(intersect(A,B))"),
--    Result "continuous functions preserve limits" [
--        parse formula "continuous(f)",
--        parse formula "tendsto(an,a)"]
--        (parse formula "tendsto(applyfnpointwise(f,an),applyfn(f,a))"),
    Result "" [
        parse formula "subset(A,ball(x,beta))",
        parse formula "atmost(beta,gamma)"]
        (parse formula "subset(A,ball(x,gamma))"),
    Result "transitivity" [
        parse formula "atmost(alpha,beta)"]
        (parse formula "subsetof(ball(x,alpha),ball(x,beta))"),
    Result "" [
        parse formula "subsetof(A,B)",
        parse formula "subsetof(B,C)"]
        (parse formula "subsetof(A,C)"),
    Result "a closed set contains its limit points" [
        parse formula "closedin(F,X)",
        parse formula "sequencein(an,F)",
        parse formula "tendsto(an,a)"]
        (parse formula "in(a,F)"),
    Result "" [parse formula "issameas(A,complement(B))"] (parse formula "equals(twoBack(f,A),complement(preimage(f,B)))")
 ][
    Solution [parse variable "eta"] [
        parse formula "atmost(eta, alpha)",
        parse formula "atmost(eta, beta)"]
        [parse term "min(alpha, beta)"]
 ]
 expansionTable
 rewriteTable

