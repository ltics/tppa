module Tactic where

import Core

type Justification = [Theorem] -> Theorem
type GoalState = ([Goal], Theorem)
type Tactic = Goal -> ([Goal], Justification)
