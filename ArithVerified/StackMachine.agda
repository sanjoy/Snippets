module StackMachine where

open import Data.Bool
open import Data.List
open import Data.Nat
open import Relation.Nullary

data TypedStack : List Set → Set₁ where
  nil : TypedStack []
  push : {A : Set} {S : List Set} → A → TypedStack S → TypedStack (A ∷ S)

bcAdd : {S : List Set} → TypedStack (ℕ ∷ ℕ ∷ S) → TypedStack (ℕ ∷ S)
bcAdd (push a (push b rest)) = push (a + b) rest

bcSub : {S : List Set} → TypedStack (ℕ ∷ ℕ ∷ S) → TypedStack (ℕ ∷ S)
bcSub (push a (push b rest)) = push (a ∸ b) rest

bcEq : {S : List Set} → TypedStack (ℕ ∷ ℕ ∷ S) → TypedStack (Bool ∷ S)
bcEq (push a (push b rest)) with Data.Nat._≟_ a b
... | yes _ = push true rest
... | no _ = push false rest

bcLt : {S : List Set} → TypedStack (ℕ ∷ ℕ ∷ S) → TypedStack (Bool ∷ S)
bcLt (push a (push b rest)) with Data.Nat._≤?_ a b
... | yes _ = push true rest
... | no _ = push false rest

bcCond : {S : List Set} {A : Set} → TypedStack (Bool ∷ A ∷ A ∷ S) →
         TypedStack (A ∷ S)
bcCond (push c (push x (push y rest))) = push (if c then x else y) rest

StackProgram : Set → Set₁
StackProgram a = {S : List Set} → TypedStack S → TypedStack (a ∷ S)
