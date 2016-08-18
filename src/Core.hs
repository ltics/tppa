module Core where

import Util
import Data.Char (chr)
import Data.List (intersperse)
import qualified Text.PrettyPrint as PP

data Formula = Var Int
             | Imp Formula Formula
             deriving(Eq)

prettify :: Formula -> String
prettify (Var n) = [chr n]
prettify (Imp f1 f2) = "(" ++ prettify f1 ++ " ⇒ " ++ prettify f2 ++ ")"

-- ord 'α' -> 945
instance Show Formula where
  showsPrec _ x = shows $ PP.text $ prettify x

type Sequent = ([Formula], Formula)

data Theorem = Provable Sequent deriving(Eq)

instance Show Theorem where
  show (Provable (l, a)) = concat (intersperse ", " (map show l)) ++ " ⊢ " ++ show a

data Goal = Goal Sequent deriving(Eq)

instance Show Goal where
  show (Goal (l, a)) = concat (intersperse ", " (map show l)) ++ " ⊢? " ++ show a

assume :: Formula -> Theorem
assume a = Provable ([a], a)

introRule :: Formula -> Theorem -> Theorem
introRule a (Provable (gamma, b)) = Provable (gamma <-> a, Imp a b)

elimRule :: Theorem -> Theorem -> Theorem
elimRule (Provable (gamma, imp)) (Provable (delta, a)) = case imp of
  Var _ -> error "cannot use [elim_rule] with (Var _) in first argument"
  Imp _ b -> case imp == Imp a b of
    True -> Provable (gamma ++ delta, b)
    False -> error "antecedent of first argument must be the second argument"
