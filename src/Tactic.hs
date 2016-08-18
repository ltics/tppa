module Tactic where

import Core

type Justification = [Theorem] -> Theorem
type GoalState = ([Goal], Theorem)
type Tactic = Goal -> ([Goal], Justification)

collapseFormulas :: [Formula] -> Formula
collapseFormulas [] = error "no formula found"
collapseFormulas (f : fs) = foldr (\x y -> Imp x y) f fs

goalToTheorem :: Goal -> Theorem
goalToTheorem (Goal (gamma, b)) = foldl (\th phi -> elimRule th $ assume phi) (assume (collapseFormulas (b : gamma))) gamma

diff :: Formula -> Formula -> [Formula]
diff f conclusion' = diff' f conclusion' []
  where diff' :: Formula -> Formula -> [Formula] -> [Formula]
        diff' f' c diff'' = case f' of
          c' | c' == c -> diff''
          Imp a b -> diff' b c (a : diff'')
          _ -> error "strip exception"

conclusion :: Theorem -> Formula
conclusion (Provable (_, f)) = f

by :: Tactic -> GoalState -> GoalState
by tac (g : gs, th@(Provable (phiG : _, _))) = (gs' ++ gs, elimRule thA thB')
  where (gs', j) = tac g
        thA = introRule phiG th
        thB = j $ map goalToTheorem gs'
        thB' = foldr introRule thB $ reverse $ diff phiG $ conclusion thB
by _ _ = error "there must be an open goal"

(|-) :: Theorem -> Formula -> Bool
(Provable (_, f')) |- f = f == f'

assumption :: forall t t1. Goal -> ([t], t1 -> Theorem)
assumption (Goal (gamma, a)) = case elem a gamma of
  True -> ([], \_ -> assume a)
  False -> error "assumption tactic not applicable"
