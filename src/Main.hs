module Main (
    main
) where

import Prelude hiding ((/))

import Control.Arrow
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.Either
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List
import Control.Monad.Logic
import Control.Monad.Trans.List
import Control.Monad.Trans.State.Lazy
import Control.Monad.Identity hiding (msum)

import Debug.Trace

import Types
import Rename
import Expansion
import Match
import TexBase
import Move
import Parser
import Tex
import RobotM
import Library
import Writeup
import Printing

import DeletionMoves
import TidyingMoves
import ApplyingMoves
import Suspension

import qualified TestData

----------------------------------------------------------------------------------------------------

moveTypesByPriority :: [MoveType]
moveTypesByPriority = [
  --Deletion
    deleteDone,
    deleteDoneDisjunct,
--    deleteRedundantHypothesis, --move 1
    deleteDangling, --move 2
    deleteUnmatchable, -- move 3
  --Tidying (4-9)
    peelAndSplitUniversalConditionalTarget, --move 4
--    flipNegativeTarget, --move 5
--    flipNegativeHypothesis, --move 6
    splitDisjunctiveHypothesis, --move 7
--    splitConjunctiveTarget, --move 8
    splitDisjunctiveTarget,
    peelBareUniversalTarget, -- move 9
    removeTarget, --move 10
    collapseSubtableauTarget,
  --Applying
    forwardsReasoning, --move 11
    forwardsLibraryReasoning, --move 11
    expandPreExistentialHypothesis, --move 13
    elementaryExpansionOfHypothesis, --move 12
    backwardsReasoning, --move 14
    backwardsLibraryReasoning, --move 14
    elementaryExpansionOfTarget, --move 15
    expandPreUniversalTarget, --move 16
    solveBullets,
    automaticRewrite,
  --Suspension
    unlockExistentialUniversalConditionalTarget, --move 17
    unlockExistentialTarget,
    expandPreExistentialTarget,
    convertDiamondToBullet,
    rewriteVariableVariableEquality,
    rewriteVariableTermEquality
  ]

allMovesByPriority :: Tableau -> [RobotM (MoveDescription, Tableau)]
allMovesByPriority  t = [f t | (MoveType f) <- moveTypesByPriority]

----------------------------------------------------------------------------------------------------

lengthAtLeast :: Int -> [a] -> Bool
lengthAtLeast 0 _      = True
lengthAtLeast _ []     = False
lengthAtLeast n (_:xs) = lengthAtLeast (n-1) xs

----------------------------------------------------------------------------------------------------

printMax = 100

main = do
    let pd = TestData.printingData
        lib = TestData.library

    let movesFrom :: RobotState -> Tableau -> [(MoveDescription, Tableau)]
        movesFrom s t = case mapMaybe (runRobotM pd lib s) (allMovesByPriority t) of
            [] -> []
            (move@(MoveDescription _ _ _, t'), s'):_ -> move:movesFrom s' t'

        solve :: Problem -> (Tableau, [(MoveDescription, Tableau)])
        solve (Problem _ hs t) =
            let initialTableauM = createTableau False (parse formula <$> hs) $ parse formula t
                Just (initialTableau, s) = runRobotM pd lib initialRobotState initialTableauM
             in (initialTableau, movesFrom s initialTableau)

        -- printMove: prints oldTableau + move text
        printMove :: Int -> Tableau -> MoveDescription -> IO ()
        printMove n oldTableau (MoveDescription statementsUsed clauses text) = do
            putStrLn . fit $ texTableauBolding pd statementsUsed oldTableau
            putStrLn "\\smallskip"
            putStrLn ""
            putStrLn $ {-trace (show n ++ ". " ++ text) $-} "\\noindent" ++ show n ++ ". " ++ text ++ "\\nopagebreak[4] "
            putStrLn $ "\\marginpar{" ++ unwords (asSentence . writeup pd <$> clauses) ++ "}" ++ "\\nopagebreak[4] "
            putStrLn $ "\\smallskip" ++ "\\nopagebreak[4] "
            putStrLn ""

        printSolution :: Int -> Problem -> IO ()
        printSolution max p =
          let (initialTableau, moves) = solve p
              (moveDescriptions, outputTableaux) = unzip moves
              proof = compress . eliminate . fuse $ concat [cs | MoveDescription _ cs _ <- moveDescriptions]

          in  if null moves
                then putStrLn (fit $ tex pd initialTableau) >> putStrLn "No moves possible."
                else do
        --            putStrLn "\\begin{center}"
        --            putStrLn "\\vspace{-3mm}"
        --            putStrLn . fit $ tex initialTableau
        --            putStrLn "\\end{center}"
                    when (not $ lengthAtLeast (max+1) moves) $ do
                        putStrLn "\\begin{center}"
                        putStrLn "\\begin{minipage}{120mm}"
                        putStrLn . unwords $ asSentence . writeup pd <$> proof
                        putStrLn "\\end{minipage}"
                        putStrLn "\\end{center}"
                        putStrLn ""
                        putStrLn "\\bigskip"

                    putStrLn "\\begin{steps}"
                    sequence_ $ zipWith3 printMove [1..max] (initialTableau:outputTableaux) moveDescriptions
                    putStrLn . fit . tex pd . last . take max $ outputTableaux --print final tableau
                    putStrLn ""
                    if lengthAtLeast (max+1) moves
                      then putStrLn $ show max ++ " moves made; stopping as the Robot may be in an infinite loop."
                      else case last moves of
                        (_, Done _) -> trace ("\t" ++ show (length moves) ++ " moves made; problem solved.") $
                                         putStrLn "Problem solved."
                        _ -> trace ("\t" ++ show (length moves) ++ " moves made.") $
                                         putStrLn "No moves possible."
                    putStrLn "\\cleardoublepage\n"
                    putStrLn "\\end{steps}" --}

        attemptProblem :: Problem -> IO ()
        attemptProblem p@(Problem description _ _) = do
        --    putStrLn "\\vspace{-3mm}"
            putStrLn $ "{\\begin{center} \\large " ++ textbf description ++ "\\end{center}}\\nopagebreak[4]"
            putStrLn ""
            printSolution printMax p


    putStrLn texHeader
    mapM_ attemptProblem TestData.problems
    putStrLn texFooter

----------------------------------------------------------------------------------------------------
