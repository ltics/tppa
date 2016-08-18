module Core where

import Util

data Formula = Var Int
             | Imp (Formula, Formula)
             deriving(Eq, Show)

type Sequent = ([Formula], Formula)

data Theorem = Provable Sequent deriving(Eq, Show)

data Goal = Goal Sequent deriving(Eq, Show)

assume :: Formula -> Theorem
assume a = Provable ([a], a)

introRule :: Formula -> Theorem -> Theorem
introRule a (Provable (gamma, b)) = Provable (gamma <-> a, Imp (a, b))

elimRule :: Theorem -> Theorem -> Theorem
elimRule (Provable (gamma, imp)) (Provable (delta, a)) = case imp of
  Var _ -> error "cannot use [elim_rule] with (Var _) in first argument"
  Imp (_, b) -> case imp == Imp (a, b) of
    True -> Provable (gamma ++ delta, b)
    False -> error "antecedent of first argument must be the second argument"
