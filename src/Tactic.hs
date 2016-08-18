module Tactic where

import Util
import Core
import Control.Monad

type Justification = [Theorem] -> Either Exception Theorem
type GoalState = ([Goal], Theorem)
type Tactic = Goal -> Either Exception ([Goal], Justification)

collapseFormulas :: [Formula] -> Formula
collapseFormulas [] = error "no formula found"
collapseFormulas (f : fs) = foldr (\x y -> Imp x y) f fs

goalToTheorem :: Goal -> Either Exception Theorem
goalToTheorem (Goal (gamma, b)) = foldM (\th phi -> elimRule th $ assume phi) (assume (collapseFormulas (b : gamma))) gamma

diff :: Formula -> Formula -> Either Exception [Formula]
diff f conclusion' = diff' f conclusion' []
  where diff' :: Formula -> Formula -> [Formula] -> Either Exception [Formula]
        diff' f' c diff'' = case f' of
          c' | c' == c -> Right diff''
          Imp a b -> diff' b c (a : diff'')
          _ -> Left StripException

conclusion :: Theorem -> Formula
conclusion (Provable (_, f)) = f

by :: Tactic -> GoalState -> Either Exception GoalState
by tac (g : gs, th@(Provable (phiG : _, _))) = do (gs', j) <- tac g
                                                  let thA = introRule phiG th
                                                  ths <- mapM goalToTheorem gs'
                                                  thB <- j ths
                                                  diffUnwrap <- diff phiG $ conclusion thB
                                                  let thB' = do return $ foldr introRule thB $ reverse $ diffUnwrap
                                                  thBUnwrap' <- thB'
                                                  rule <- elimRule thA thBUnwrap'
                                                  return (gs' ++ gs, rule)
by _ _ = Left $ TacticException "there must be an open goal"

(|-) :: Theorem -> Formula -> Bool
(Provable (_, f')) |- f = f == f'

assumption :: forall t t1. Goal -> Either Exception ([t], t1 -> Theorem)
assumption (Goal (gamma, a)) = case elem a gamma of
  True -> Right ([], \_ -> assume a)
  False -> Left $ TacticException "assumption tactic not applicable"

introTac :: Tactic
introTac (Goal (gamma, imp)) = case imp of
  Var _ -> Left $ TacticException "intro tactic only works on implicative goals"
  Imp a b -> Right ([Goal (gamma ++ [a], b)], f)
    where f = \thms -> case find (\th -> th |- b) thms of
            Just th -> Right $ introRule a th
            Nothing -> Left JustificationException

elimTac :: Formula -> Tactic
elimTac a (Goal (gamma, b)) = Right ([Goal (gamma, Imp a b), Goal (gamma, a)], f)
  where f = \thms -> case (find (\th -> th |- Imp a b) thms, find (\th -> th |- a) thms) of
          (Just thImp, Just thB) -> elimRule thImp thB
          _ -> Left JustificationException

tryTac :: Tactic -> Tactic
tryTac tac g = case tac g of
  Left (TacticException _) -> Right ([g], (\ths -> case ths of
                                                   [th] -> Right th
                                                   _ -> Left JustificationException))
  t -> t