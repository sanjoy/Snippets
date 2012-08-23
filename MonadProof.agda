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


data Monad {ℓ : Level} (m : Set ℓ → Set ℓ)
           (return : {A : Set ℓ} → A → m A)
           (bind : {A B : Set ℓ} → m A → (A → m B) → m B)
           : Set (L.suc ℓ) where
  monad : (law₀ m return bind) → (law₁ m return bind) → (law₂ m bind) →
          Monad m return bind


_>>=_ : {ℓ : Level} → {A B : Set ℓ} → {m : Set ℓ → Set ℓ} →
        {return : ∀ {A} → A → m A} → {bind : ∀ {A B} → m A → (A → m B) → m B} →
        ⦃ v : Monad m return bind ⦄ → m A → (A → m B) → m B
_>>=_ {bind = bind} a b = bind a b

⟦_⟧ : {ℓ : Level} → {A : Set ℓ} → {m : Set ℓ → Set ℓ} →
      {return : ∀ {A} → A → m A} → {bind : ∀ {A B} → m A → (A → m B) → m B} →
      ⦃ v : Monad m return bind ⦄ → A → m A
⟦_⟧ {return = return} a = return a


data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  just : A → Maybe A
  nothing : Maybe A

maybeReturn : {ℓ : Level} → {A : Set ℓ} → A → Maybe A
maybeReturn = just

maybeBind : {ℓ : Level} → {A B : Set ℓ} → Maybe A → (A → Maybe B) → Maybe B
maybeBind (just y) f = f y
maybeBind nothing f = nothing

maybeMonad : Monad {L.zero} Maybe maybeReturn maybeBind
maybeMonad = monad p₀ p₁ p₂
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
stateBind {B = B} k f = new-state (λ old → ↓ (f (proj₂ (↓ k old))) (proj₁ (↓ k old)))

type : {ℓ : Level} → (A : Set ℓ) → A → A
type _ a = a

stateMonad : Monad {L.zero} State stateReturn stateBind
stateMonad = monad p₀ p₁ p₂
  where p₀ : {ℓ : Level} → (A B : Set ℓ) → (a : A) → (f : A → State B) → 
             (stateBind (stateReturn a) f) ≡ f a
        p₀ A B a f = let equiv₀ : (↓ (stateReturn a) ≡ ↓ (stateReturn a))
                         equiv₀ = refl
                         main : (stateBind (stateReturn a) f) ≡
                                new-state (λ old → ↓ (f a) old)
                         main = cong (λ k → new-state
                                        (λ old →
                                          ↓ (f (proj₂ (k old)))
                                          (proj₁ (k old)))) equiv₀
                     in trans main (elim (f a))
           where elim : (f : State B) → (new-state (λ old → ↓ f old) ≡ f)
                 elim f = let a = cong (λ t → ↓ t) (type (f ≡ f) refl)
                              b : ((λ old → ↓ f old) ≡ ↓ f)
                              b = cong (λ t → (λ old → t old)) a
                              equiv₁ : (a : State B) → new-state (↓ a) ≡ a
                              equiv₁ _ = refl
                          in trans (cong (λ t → new-state t) b) (equiv₁ f)

        p₁ : {ℓ : Level} → (A : Set ℓ) → (a : A) → (v : State A) →
             (stateBind v stateReturn) ≡ v
        p₁ {ℓ = ℓ} A a k =
              let lem₀ : (λ (a : ℕ × A) →
                       ↓ (stateReturn (proj₂ a)) (proj₁ a)) ≡
                        λ (a : ℕ × A) → ↓ (new-state λ n → (n , proj₂ a)) (proj₁ a)
                  lem₀ = cong (λ t (a : ℕ × A) → ↓ (t (proj₂ a)) (proj₁ a)) (type (
                          (λ s → stateReturn s) ≡ (λ s → new-state λ n → (n , s))) refl)
                  lem₁ : (λ (a : ℕ × A) → ↓ (new-state λ n → (n , proj₂ a)) (proj₁ a)) ≡
                                            (λ (a : ℕ × A) → (λ n → (n , proj₂ a)) (proj₁ a))
                  lem₁ = cong (λ t → 
                               (λ (a : ℕ × A) → (t (λ n → (n , proj₂ a))) (proj₁ a)))
                         (type ((λ x → ↓ (new-state x)) ≡ (λ x → x)) refl)
                  lem-id : (λ (a : ℕ × A) → ↓ (stateReturn (proj₂ a)) (proj₁ a)) ≡
                                             λ (a : ℕ × A) → (proj₁ a , proj₂ a)
                  lem-id = (trans lem₀ lem₁)
              in cong (λ t → new-state (λ old → t (↓ k old))) lem-id

        p₂ : {ℓ : Level} → (A B C : Set ℓ) → (a : State A) → (f : A → State B) →
             (g : B → State C) → (stateBind (stateBind a f) g) ≡ 
             (stateBind a (λ x → (stateBind (f x) g)))
        p₂ A B C a f g = let t₀ : (stateBind (stateBind a f) g) ≡
                                  (new-state (λ old →
                                    ↓ (g (proj₂
                                         (↓ (f (proj₂ (↓ a old))) (proj₁ (↓ a old)))))
                                    (proj₁ (↓ (f (proj₂ (↓ a old))) (proj₁ (↓ a old))))))
                             t₀ = refl
                             t₁ : (stateBind a (λ x → (stateBind (f x) g))) ≡
                                  (new-state (λ old →
                                    ↓ (g (proj₂ (↓ (f (proj₂ (↓ a old)))
                                                  (proj₁ (↓ a old)))))
                                    (proj₁ (↓ (f (proj₂ (↓ a old))) (proj₁ (↓ a old))))))
                             t₁ = refl
            in trans t₀ (sym t₁)

getState : State ℕ
getState = new-state (λ n → (n , n))

record Unit : Set where

putState : ℕ → State Unit
putState n = new-state (λ _ → (n , _))

-- I can't get it to work with ⟦ ⟧ and >>=, probably because of some
-- clashes with the maybe monad declaration.  I'm not sure how this
-- can be fixed.

testState : State ℕ
testState = stateReturn 42
