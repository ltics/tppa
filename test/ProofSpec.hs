module ProofSpec where

import Core
import Tactic
import Test.Hspec

runProofSpec :: Formula -> Theorem -> IO ()
runProofSpec target top = top `shouldBe` Provable ([], target)

spec :: Spec
spec = do
  describe "proof test" $ do
    it "proof a formula to a theorem" $ do
      g $ theorem "A ⇒ B ⇒ A"
      e $ repeatTac introTac
      e assumption
      topTheorem >>= (runProofSpec $ Imp (Var 65) (Imp (Var 66) (Var 65)))

      g $ theorem "A ⇒ (A ⇒ B) ⇒ B"
      e $ repeatTac introTac
      e $ elimTac $ theorem "A"
      e assumption
      e assumption
      topTheorem >>= (runProofSpec $ Imp (Var 65) (Imp (Imp (Var 65) (Var 66)) (Var 66)))

      g $ theorem "A ⇒ (B ⇒ C) ⇒ (A ⇒ B) ⇒ C"
      e $ repeatTac introTac
      e $ elimTac $ theorem "B"
      e assumption
      e $ elimTac $ theorem "A"
      e assumption
      e assumption
      topTheorem >>= (runProofSpec $ Imp (Var 65) (Imp (Imp (Var 66) (Var 67)) (Imp (Imp (Var 65) (Var 66)) (Var 67))))
