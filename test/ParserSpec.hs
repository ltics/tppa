module ParserSpec where

import Parser
import Core
import Test.Hspec

spec :: Spec
spec = do
  describe "parser test" $ do
    it "parse formula" $ do
      parseExpr "A ⇒ B ⇒ A" `shouldBe` Imp (Var 65) (Imp (Var 66) (Var 65))
      parseExpr "A ⇒ (A ⇒ B) ⇒ B" `shouldBe` Imp (Var 65) (Imp (Imp (Var 65) (Var 66)) (Var 66))
      parseExpr "A ⇒ (B ⇒ C) ⇒ (A ⇒ B) ⇒ C" `shouldBe` Imp (Var 65) (Imp (Imp (Var 66) (Var 67)) (Imp (Imp (Var 65) (Var 66)) (Var 67)))
