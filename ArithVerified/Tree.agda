module Tree where

open import Data.Bool
open import Data.Nat
open import Relation.Nullary

data Exp : Set → Set₁ where
  ↑_ : {A : Set} → A → Exp A
  _plus_ : Exp ℕ → Exp ℕ → Exp ℕ
  _minus_ : Exp ℕ → Exp ℕ → Exp ℕ
  _eq_ : Exp ℕ → Exp ℕ → Exp Bool
  _lt_ : Exp ℕ → Exp ℕ → Exp Bool
  cond_then_else_ : {A : Set} → Exp Bool → Exp A → Exp A → Exp A

eval : {A : Set} → Exp A → A
eval (↑ value) = value
eval (a plus b) = eval a + eval b
eval (a minus b) = eval a ∸ eval b
eval (a eq b) with Data.Nat._≟_ (eval a) (eval b)
... | yes _ = true
... | no _ = false
eval (a lt b) with Data.Nat._≤?_ (eval a) (eval b)
... | yes _ = true
... | no _ = false
eval (cond c then t else f) = if eval c then eval t else eval f
