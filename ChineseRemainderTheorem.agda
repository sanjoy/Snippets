module ChineseRemainderTheorem where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

data _is_mod_ (a b n : ℕ) : Set where
  mod : (k : ℕ) → a ≡ (b + k * n) → a is b mod n

