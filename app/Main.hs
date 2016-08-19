module Main where

import Tactic

main :: IO ()
main = do g $ formula "A ⇒ B ⇒ A"
          e $ repeatTac introTac
          e assumption
          topTheorem >>= print

          g $ formula "A ⇒ (A ⇒ B) ⇒ B"
          e $ repeatTac introTac
          e $ elimTac $ formula "A"
          e assumption
          e assumption
          topTheorem >>= print

          g $ formula "A ⇒ (B ⇒ C) ⇒ (A ⇒ B) ⇒ C"
          e $ repeatTac introTac
          e $ elimTac $ formula "B"
          e assumption
          e $ elimTac $ formula "A"
          e assumption
          e assumption
          topTheorem >>= print

