module TAL0 where

open import Data.Vec
open import Data.Nat
open import Coinduction
open import Data.Fin as F hiding(_+_)
open import Relation.Binary.PropositionalEquality
open import Level as L
open import Data.Bool

size : ℕ
size = 2

Reg = F.Fin size

mutual
  Γ′ : ℕ → Set
  Γ′ n = Vec Type n

  Γ = Γ′ size

  data Type : Set where
    natType : Type
    blockType : Γ′ size → Type
    anything : Type

triviallyTrue₀ : natType ≡ natType
triviallyTrue₀ = refl

triviallyTrue₁ : {γ : Γ } → blockType γ ≡ blockType γ
triviallyTrue₁ = refl

data ⊥ : Set where
record ⊤ : Set where

equalT : Type → Type → Bool
equalT natType natType = true
equalT (blockType y) (blockType y') = equate y y'
  where equate : {n : ℕ} → Γ′ n → Γ′ n → Bool
        equate [] [] = true
        equate (x ∷ xs) (x' ∷ xs') = 
          if (equalT x x') then (equate xs xs') else false
equalT anything anything = true
equalT _ _ = false

safeToJump : {n : ℕ} → (to : Γ′ n) → (from : Γ′ n) → Set
safeToJump [] [] = ⊤
safeToJump (anything ∷ xs) (x' ∷ xs') = safeToJump xs xs'
safeToJump (x ∷ xs) (x' ∷ xs') = 
  if (equalT x x') then (safeToJump xs xs') else ⊥

safeToJump' : Γ → Reg → Set
safeToJump' γ idx with lookup idx γ
... | natType = ⊥
... | blockType γ′ = safeToJump γ′ γ
... | anything = ⊥

data Block : Γ → Set where
  jump : {γ₀ γ₁ : Γ} → ∞ (Block γ₀) -> { _ : safeToJump γ₀ γ₁ } → Block γ₁
  _←r_▶_ : {γ : Γ} → (dest : Reg) → (src : Reg) →
            Block (γ [ dest ]≔ (lookup src γ)) →  Block γ
  _←l_▶_ : {γ γ₀ : Γ} → (dest : Reg) → (src : ∞ (Block γ₀)) →
            Block (γ [ dest ]≔ (blockType γ₀)) →  Block γ
  _←n_▶_ : {γ : Γ} → (dest : Reg) → (src : ℕ) →
            Block (γ [ dest ]≔ natType) →  Block γ
  _←_⟨_⟩_▶_ : {γ : Γ} → (dest : Reg) → (op₀ : Reg) → 
               (fn : ℕ → ℕ → ℕ) → (op₁ : Reg) → 
               ⦃ _ : lookup op₀ γ ≡ natType ⦄ → 
               ⦃ _ : lookup op₁ γ ≡ natType ⦄ → 
               Block (γ [ dest ]≔ natType) → Block γ
  if_jump_▶ : {γ : Γ} → (src : Reg) → (dest : Reg) →
              ⦃ _ : lookup src γ ≡ natType ⦄ → 
              { _ : safeToJump' γ dest } →
              Block γ → Block γ

⟦_⟧ : ∀ {n} → (m : ℕ) → Fin ((1 + m) + n)
⟦ 0 ⟧ = F.zero
⟦ (ℕ.suc n) ⟧ = F.suc ⟦ n ⟧

mutual
  a : Block (natType ∷ blockType (anything ∷ natType ∷ []) ∷ [])
  a = ⟦ 0 ⟧ ←r ⟦ 1 ⟧ ▶
      (⟦ 1 ⟧ ←n 42 ▶
       (if ⟦ 1 ⟧ jump ⟦ 0 ⟧ ▶
        (jump (♯ b))))

  b : Block (anything ∷ natType ∷ [])
  b = jump (♯ b)

mutual
  α : Block (natType ∷ natType ∷ [])
  α = jump (♯ β)
  β : Block (natType ∷ natType ∷ [])
  β = jump (♯ α)
