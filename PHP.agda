module PHP where

open import Data.Nat
open import Data.Fin as F
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

lemma-single-value : (k l : F.Fin 1) → k ≡ l
lemma-single-value zero zero = refl
lemma-single-value zero (suc ())
lemma-single-value (suc ()) _

data Sum (A : Set) (B : Set) : Set where
  left : A → Sum A B
  right : B → Sum A B

--finite-filter : (f : ℕ → ℕ) → (lim : ℕ) → (v : ℕ) → Sum (Σ ℕ (λ n → f 

PHP : (n : ℕ) → (f : F.Fin (suc (suc n)) → F.Fin (suc n)) →
  Σ (F.Fin (suc (suc n)) × F.Fin (suc (suc n)))
    (λ tup → (proj₁ tup) ≢ (proj₂ tup) × f (proj₁ tup) ≡ f (proj₂ tup))
PHP zero f = (zero , F.suc zero) , (λ ()) , (lemma-single-value (f zero) (f (suc zero)))
PHP (suc n) f = {!!}
