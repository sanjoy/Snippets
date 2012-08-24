module MonadProof where

open import Level as L
open import Data.Nat hiding(_⊔_)
open import Relation.Binary.PropositionalEquality

-- A consistency proof of the Maybe and State monads.

law₀ : {ℓ : Level} → (m : Set ℓ → Set ℓ) → ({A : Set ℓ} → A → m A) →
                     ({A B : Set ℓ} → m A → (A → m B) → m B) → Set (L.suc ℓ)
law₀ {ℓ} m return bind = (A B : Set ℓ) → (a : A) → (f : A → m B) → 
                         (bind (return a) f) ≡ f a

law₁ : {ℓ : Level} → (m : Set ℓ → Set ℓ) → ({A : Set ℓ} → A → m A) →
                     ({A B : Set ℓ} → m A → (A → m B) → m B) → Set (L.suc ℓ)
law₁ {ℓ} m return bind = (A : Set ℓ) → (a : A) → (v : m A) → (bind v return) ≡ v

law₂ : {ℓ : Level} → (m : Set ℓ → Set ℓ) →
                     ({A B : Set ℓ} → m A → (A → m B) → m B) → Set (L.suc ℓ)
law₂ {ℓ} m bind = (A B C : Set ℓ) → (a : m A) → (f : A → m B) → (g : B → m C) →
                  (bind (bind a f) g) ≡ (bind a (λ x → (bind (f x) g)))


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

maybeReturn : {ℓ : Level} → {A : Set ℓ} → A → Maybe A
maybeReturn = just

maybeBind : {ℓ : Level} → {A B : Set ℓ} → Maybe A → (A → Maybe B) → Maybe B
maybeBind (just y) f = f y
maybeBind nothing f = nothing

maybeMonad : Monad {L.zero} Maybe
maybeMonad = monad maybeReturn maybeBind p₀ p₁ p₂
  where p₀ : {ℓ : Level} → (A B : Set ℓ) → (a : A) → (f : A → Maybe B) → 
             (maybeBind (maybeReturn a) f) ≡ f a
        p₀ _ _ _ _ = refl

        p₁ : {ℓ : Level} → (A : Set ℓ) → (a : A) → (v : Maybe A) →
             (maybeBind v maybeReturn) ≡ v
        p₁ _ _ (just y) = refl
        p₁ _ _ nothing = refl

        p₂ : {ℓ : Level} → (A B C : Set ℓ) → (a : Maybe A) → (f : A → Maybe B) →
             (g : B → Maybe C) → (maybeBind (maybeBind a f) g) ≡ 
                                   (maybeBind a (λ x → (maybeBind (f x) g)))
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

stateReturn : {ℓ : Level} → {A : Set ℓ} → A → State A
stateReturn a = new-state (λ n → (n , a))

stateBind : {ℓ : Level} → {A B : Set ℓ} → State A → (A → State B) → State B
stateBind {B = B} k f = new-state (λ old → ↓ (f (proj₂ (↓ k old)))
                        (proj₁ (↓ k old)))

type : {ℓ : Level} → (A : Set ℓ) → A → A
type _ a = a

stateMonad : Monad {L.zero} State
stateMonad = monad stateReturn stateBind p₀ p₁ p₂
  where p₀ : {ℓ : Level} → (A B : Set ℓ) → (a : A) → (f : A → State B) → 
             (stateBind (stateReturn a) f) ≡ f a
        p₀ _ _ _ _ = refl

        p₁ : {ℓ : Level} → (A : Set ℓ) → (a : A) → (v : State A) →
             (stateBind v stateReturn) ≡ v
        p₁ _ _ _ = refl

        p₂ : {ℓ : Level} → (A B C : Set ℓ) → (a : State A) → (f : A → State B) →
             (g : B → State C) → (stateBind (stateBind a f) g) ≡ 
             (stateBind a (λ x → (stateBind (f x) g)))
        p₂ _ _ _ _ _ _ = refl

getState : State ℕ
getState = new-state (λ n → (n , n))

record Unit : Set where

putState : ℕ → State Unit
putState n = new-state (λ _ → (n , _))

-- -- I can't get it to work with ⟦ ⟧ and >>=, probably because of some
-- -- clashes with the maybe monad declaration.  I'm not sure how this
-- -- can be fixed.

testState : State ℕ
testState = stateReturn 42
