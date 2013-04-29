module Compile where

open import Data.Bool
open import Data.List
open import Data.Nat
open import Function
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import StackMachine
open import Tree

compile : {A : Set} → Exp A → StackProgram A
compile (↑ y) = push y
compile (a plus b) = bcAdd ∘ compile a ∘ compile b
compile (a minus b) = bcSub ∘ compile a ∘ compile b
compile (a eq b) = bcEq ∘ compile a ∘ compile b
compile (a lt b) = bcLt ∘ compile a ∘ compile b
compile (cond c then x else y) = bcCond ∘ compile c ∘ compile x ∘ compile y

IsCorrectFor : {A : Set} → Exp A → Set₁
IsCorrectFor exp = (S : List Set) → (compile exp {S} ≡ push{_}{S} (eval exp))

condEqHelper : (S : List Set) → (a b : Exp ℕ) →
             bcEq{S} ∘ (push (eval a)) ∘ (push (eval b)) ≡ (push (eval (a eq b)))
condEqHelper S a b with Data.Nat._≟_ (eval a) (eval b)
... | yes p = refl
... | no ¬p = refl

condLtHelper : (S : List Set) → (a b : Exp ℕ) →
             bcLt{S} ∘ (push (eval a)) ∘ (push (eval b)) ≡ (push (eval (a lt b)))
condLtHelper S a b with Data.Nat._≤?_ (eval a) (eval b)
... | yes p = refl
... | no ¬p = refl

verifyCompiler : {A : Set} → (exp : Exp A) → IsCorrectFor exp
verifyCompiler (↑ y) S = refl
verifyCompiler (a plus b) S =
  let inductionA = verifyCompiler a
      inductionB = verifyCompiler b
      sub-prf₀ = subst (λ term → compile (a plus b) ≡ bcAdd ∘ compile a ∘ term)
                 (inductionB S) refl
      sub-prf₁ = subst (λ term → bcAdd ∘ compile a ∘ (push (eval b)) ≡
                        bcAdd ∘ term ∘ (push (eval b)))
                 (inductionA (ℕ ∷ S)) refl
  in trans sub-prf₀ sub-prf₁
verifyCompiler (a minus b) S =
  let inductionA = verifyCompiler a
      inductionB = verifyCompiler b
      sub-prf₀ = subst (λ term → compile (a minus b) ≡ bcSub ∘ compile a ∘ term)
                 (inductionB S) refl
      sub-prf₁ = subst (λ term → bcSub ∘ compile a ∘ (push (eval b)) ≡
                        bcSub ∘ term ∘ (push (eval b)))
                 (inductionA (ℕ ∷ S)) refl
  in trans sub-prf₀ sub-prf₁
verifyCompiler (a eq b) S =
  let inductionA = verifyCompiler a
      inductionB = verifyCompiler b
      sub-prf₀ = subst (λ term → compile (a eq b) ≡ bcEq ∘ compile a ∘ term)
                 (inductionB S) refl
      sub-prf₁ = subst (λ term → bcEq ∘ compile a ∘ (push (eval b)) ≡
                        bcEq ∘ term ∘ (push (eval b)))
                 (inductionA (ℕ ∷ S)) refl
      sub-prf₂ = condEqHelper S a b
  in trans (trans sub-prf₀ sub-prf₁) sub-prf₂
verifyCompiler (a lt b) S =
  let inductionA = verifyCompiler a
      inductionB = verifyCompiler b
      sub-prf₀ = subst (λ term → compile (a lt b) ≡ bcLt ∘ compile a ∘ term)
                 (inductionB S) refl
      sub-prf₁ = subst (λ term → bcLt ∘ compile a ∘ (push (eval b)) ≡
                        bcLt ∘ term ∘ (push (eval b)))
                 (inductionA (ℕ ∷ S)) refl
      sub-prf₂ = condLtHelper S a b
  in trans (trans sub-prf₀ sub-prf₁) sub-prf₂
verifyCompiler (cond c then a else b) S =
  let inductionA = verifyCompiler a
      inductionB = verifyCompiler b
      inductionC = verifyCompiler c
      sub-prf₀ = subst (λ term → compile (cond c then a else b)
                               ≡ bcCond ∘ compile c ∘ compile a ∘ term)
                 (inductionB S) refl
      sub-prf₁ = subst (λ term → bcCond ∘ compile c ∘ compile a ∘ (push (eval b))
                        ≡ bcCond{S} ∘ compile c ∘ term ∘ (push (eval b)))
                 (inductionA _) refl
      sub-prf₂ = subst (λ term → bcCond ∘ compile c ∘ (push (eval a)) ∘ (push (eval b))
                        ≡ bcCond{S} ∘ term ∘ (push (eval a)) ∘ (push (eval b)))
                 (inductionC _) refl
  in trans (trans sub-prf₀ sub-prf₁) sub-prf₂
