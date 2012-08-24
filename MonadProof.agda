module MonadProof where

open import Level as L
open import Data.Nat hiding(_⊔_)
open import Relation.Binary.PropositionalEquality

-- A consistency proof of the Maybe and State monads.

record Monad {ℓ : Level} (m : Set ℓ → Set ℓ) : Set (L.suc ℓ) where
  constructor monad
  field
    return : {A : Set ℓ} → A → m A
    bind : {A B : Set ℓ} → m A → (A → m B) → m B
    p₀ : (A B : Set ℓ) → (a : A) → (f : A → m B) → (bind (return a) f) ≡ f a
    p₁ : (A : Set ℓ) → (a : A) → (v : m A) → (bind v return) ≡ v
    p₂ : (A B C : Set ℓ) → (a : m A) → (f : A → m B) → (g : B → m C) → 
         (bind (bind a f) g) ≡ (bind a (λ x → (bind (f x) g)))


_>>=_ : {ℓ : Level} → {A B : Set ℓ} → {m : Set ℓ → Set ℓ} →
        ⦃ v : Monad m ⦄ →  m A → (A → m B) → m B
_>>=_ ⦃ v = v ⦄ a b = Monad.bind v a b

⟦_⟧ : {ℓ : Level} → {A : Set ℓ} → {m : Set ℓ → Set ℓ} →
      ⦃ v : Monad m ⦄ → A → m A
⟦_⟧ ⦃ v = v ⦄ a = Monad.return v a


data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  just : A → Maybe A
  nothing : Maybe A

maybeMonad : Monad {L.zero} Maybe
maybeMonad = monad just bind p₀ p₁ p₂
  where bind : {ℓ : Level} → {A B : Set ℓ} → Maybe A → (A → Maybe B) → Maybe B
        bind (just y) f = f y
        bind nothing f = nothing
        
        p₀ : {ℓ : Level} → (A B : Set ℓ) → (a : A) → (f : A → Maybe B) → 
             (bind (just a) f) ≡ f a
        p₀ _ _ _ _ = refl

        p₁ : {ℓ : Level} → (A : Set ℓ) → (a : A) → (v : Maybe A) →
             (bind v just) ≡ v
        p₁ _ _ (just y) = refl
        p₁ _ _ nothing = refl

        p₂ : {ℓ : Level} → (A B C : Set ℓ) → (a : Maybe A) → (f : A → Maybe B) →
             (g : B → Maybe C) → (bind (bind a f) g) ≡ 
                                   (bind a (λ x → (bind (f x) g)))
        p₂ A B C (just y) f g = refl
        p₂ A B C nothing f g = refl

testMaybe : Maybe ℕ
testMaybe = nothing >>= (λ x →
            ⟦(x + 1)⟧)

record _×_ {ℓ₀ ℓ₁ : Level} (A : Set ℓ₀) (B : Set ℓ₁) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

proj₁ : {ℓ₀ ℓ₁ : Level} {A : Set ℓ₀} {B : Set ℓ₁} → A × B → A
proj₁ = _×_.proj₁
proj₂ : {ℓ₀ ℓ₁ : Level} {A : Set ℓ₀} {B : Set ℓ₁} → A × B → B
proj₂ = _×_.proj₂

record State {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constructor new-state
  field
    state : (ℕ → ℕ × A)

↓ : {ℓ : Level} {A : Set ℓ} → State A → ℕ → ℕ × A
↓ = State.state

type : {ℓ : Level} → (A : Set ℓ) → A → A
type _ a = a

stateMonad : Monad {L.zero} State
stateMonad = monad return bind p₀ p₁ p₂
  where return : {ℓ : Level} → {A : Set ℓ} → A → State A
        return a = new-state (λ n → (n , a))

        bind : {ℓ : Level} → {A B : Set ℓ} → State A → (A → State B) → State B
        bind {B = B} k f = new-state (λ old → ↓ (f (proj₂ (↓ k old)))
                           (proj₁ (↓ k old)))

        p₀ : {ℓ : Level} → (A B : Set ℓ) → (a : A) → (f : A → State B) → 
             (bind (return a) f) ≡ f a
        p₀ _ _ _ _ = refl

        p₁ : {ℓ : Level} → (A : Set ℓ) → (a : A) → (v : State A) →
             (bind v return) ≡ v
        p₁ _ _ _ = refl

        p₂ : {ℓ : Level} → (A B C : Set ℓ) → (a : State A) → (f : A → State B) →
             (g : B → State C) → (bind (bind a f) g) ≡ 
             (bind a (λ x → (bind (f x) g)))
        p₂ _ _ _ _ _ _ = refl

getState : State ℕ
getState = new-state (λ n → (n , n))

record Unit : Set where

putState : ℕ → State Unit
putState n = new-state (λ _ → (n , _))

-- -- I can't get it to work with ⟦ ⟧ and >>=, probably because of some
-- -- clashes with the maybe monad declaration.  I'm not sure how this
-- -- can be fixed.

-- testState : State ℕ
-- testState = ⟦ 42 ⟧
