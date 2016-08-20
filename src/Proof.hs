module Proof where

import Core
import Tactic
import Util
import Parser
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

history :: IORef [GoalState]
history = unsafePerformIO $ newIORef []

currentGoalState :: IO GoalState
currentGoalState = do stats <- readIORef history
                      putStrLn $ show stats
                      case stats of
                        (gs : _) -> return gs
                        _ -> error "no goal state found"

printGoalState :: GoalState -> IO ()
printGoalState ([], _) = putStr "\n  No subgoals\n\n"
printGoalState (goals, th) =
  do putStr "\n  Subgoals:\n"
     mapM_ (\(i, g) -> putStr $ "    " ++ show i ++ ". " ++ show g ++ "\n") $ enumerate goals
     putStr "\n  State:\n"
     putStr $ "    " ++ show th ++ "\n\n"

p :: IO ()
p = currentGoalState >>= printGoalState

f :: Formula -> IO ()
f a = do writeIORef history [([Goal ([], a)], assume a)]
         p

e :: Tactic -> IO ()
e tac = do stats <- readIORef history
           case stats of
             (gs : t) -> case by tac gs of
                          Left _ -> error "apply tactic to subgoal failed"
                          Right gs' -> writeIORef history (gs' : gs : t) >> p
             _ -> error "no goal state found"

b :: IO ()
b = do stats <- readIORef history
       case stats of
         (_ : prev : t) -> writeIORef history (prev : t) >> p
         _ -> p

topTheorem :: IO Theorem
topTheorem = do (_, th) <- currentGoalState
                return th

theorem :: String -> Formula
theorem = parseExpr
