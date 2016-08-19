module Main where

import Tactic

main :: IO ()
main = do g $ theorem "A ⇒ B ⇒ A"
          e $ repeatTac introTac
          e assumption
          topTheorem >>= print

          g $ theorem "A ⇒ (A ⇒ B) ⇒ B"
          e $ repeatTac introTac
          e $ elimTac $ theorem "A"
          e assumption
          e assumption
          topTheorem >>= print

          g $ theorem "A ⇒ (B ⇒ C) ⇒ (A ⇒ B) ⇒ C"
          e $ repeatTac introTac
          e $ elimTac $ theorem "B"
          e assumption
          e $ elimTac $ theorem "A"
          e assumption
          e assumption
          topTheorem >>= print

