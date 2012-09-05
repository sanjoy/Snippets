module LogicalLabyrinths where

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data ⊥ : Set where

data Person : Set where
  knight : Person
  knave : Person

says : Person → Set → Set
says knight p = p
says knave p = p → ⊥

data Solution₀ : Set where
  soln₀ : (a : Person) → (b : Person) → (c : Person) →
          (says b (says a (a ≡ knave))) → (says c (b ≡ knave)) →
          Solution₀

solution₀ : Solution₀
solution₀ = soln₀ knight knave knight (λ ()) refl

Prp : Set₁
Prp = Person → Set

record _∧_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

prj₁ : {A : Set} {B : Set} → A ∧ B → A
prj₁ = _∧_.proj₁
prj₂ : {A : Set} {B : Set} → A ∧ B → B
prj₂ = _∧_.proj₂


_⇔_ : Set → Set → Set
_⇔_ a b = (a → b) ∧ (b → a)

data PredicateTransform : Set₁ where
  predicateTrans : (f : Prp → Prp) → 
                   ((OldP : Prp) → (p : Person) →
                    (OldP p) ⇔ (says p ((f OldP) p))) →
                   PredicateTransform

elim-double-neg : {A : Set} → ((A → ⊥) → ⊥) → A
elim-double-neg = {!!}

soln₁ : PredicateTransform
soln₁ = predicateTrans f proof
  where f : Prp → Prp
        f q p = says p (q p)
        proof₀ : (A : Prp) → (p : Person) → (A p) → (says p ((f A) p))
        proof₀ A knight prf = prf
        proof₀ A knave prf = λ z → z prf
        proof₁ : (A : Prp) → (p : Person) → (says p ((f A) p)) → (A p)
        proof₁ A knight prf = prf
        proof₁ A knave prf = elim-double-neg prf
        proof : (A : Prp) → (p : Person) → (A p) ⇔ (says p ((f A) p))
        proof A p = proof₀ A p , proof₁ A p

to-double-neg : {A : Set} → ((A → knave ≡ knight) → ⊥) → ((A → ⊥) → ⊥)
to-double-neg prf a = prf (λ p → f (a p))
              where f : ⊥ → knave ≡ knight
                    f ()

soln₂ : PredicateTransform
soln₂ = predicateTrans f proof
  where f : Prp → Prp
        f q p = (p ≡ knight) ⇔ (q p)
        elim-inequality : (knave ≡ knight) → ⊥
        elim-inequality = λ ()
        elim-true : {A B : Set} → A → (A ∧ B → ⊥) → (B → ⊥)
        elim-true a neg b = neg (a , b)
        p₀ : (A : Prp) (p : Person) → A p → says p (f A p)
        p₀ A knight prf = (λ x → prf) , (λ x → refl)
        p₀ A knave prf = λ p → elim-inequality ((prj₂ p) prf)
        p₁ : (A : Prp) (p : Person) → says p (f A p) → A p
        p₁ A knight prf = prj₁ prf refl
        p₁ A knave prf = elim-double-neg (to-double-neg (elim-true (λ ()) prf))
        proof : (A : Prp) (p : Person) → A p ⇔ says p (f A p)
        proof A p = p₀ A p , p₁ A p
