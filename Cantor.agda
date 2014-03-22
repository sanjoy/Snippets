module Cantor where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

data ⊥ : Set where

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ p = p → ⊥

data Bit : Set where
  Z : Bit -- "
  O : Bit -- "

flip : Bit → Bit
flip Z = O
flip O = Z

ℝ : Set
ℝ = ℕ → Bit

Ω : Set
Ω = ℕ → ℝ

data Different (a b : ℝ) : Set where
  different : (n : ℕ) → ¬ (a n ≡ b n) → Different a b

data NonExistent (order : Ω)  (r : ℝ) : Set where
  non-existent : ((n : ℕ) → Different (order n) r) →
                   NonExistent order r

construct : Ω → ℝ
construct f = λ n → flip (f n n)

flip-lemma : (x : Bit) → ¬ (x ≡ flip x)
flip-lemma Z ()
flip-lemma O ()

cantor : (o : Ω) → Σ ℝ (λ r → NonExistent o r)
cantor o = construct o , non-existent (
             λ n → different n (flip-lemma (o n n)))
