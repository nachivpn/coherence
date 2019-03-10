module Coherence where

open import CCC

-- normal forms for the Hom language
data Nf (C : Ty) : Ty → Set where
  unit : Nf C 𝟏
  abs  : ∀ {A B} → Nf (C * A) B → Nf C (A ⇒ B)
  pair : ∀ {A B} → Nf C A → Nf C B → Nf C (A * B)

module NBE where

  open import Data.Unit using (⊤ ; tt)
  open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)

  ⟦_⟧ : Ty → Set
  ⟦ 𝟏 ⟧      = ⊤
  ⟦ t ⇒ t₁ ⟧ = ⟦ t ⟧ → ⟦ t₁ ⟧
  ⟦ t * t₁ ⟧ = ⟦ t ⟧ × ⟦ t₁ ⟧

  reflect : ∀ (A : Ty) → ⟦ A ⟧
  reflect 𝟏       = tt
  reflect (A ⇒ B) = λ x → reflect B
  reflect (A * B) = reflect A , reflect B

  reify :  ∀ {A Γ} → ⟦ A ⟧ → Nf Γ A
  reify {𝟏}     t = unit
  reify {A ⇒ B} t = abs (reify (t (reflect A)))
  reify {A * B} t = pair (reify (proj₁ t)) (reify (proj₂ t))

  eval :  ∀ {a c} → Hom c a → (⟦ c ⟧ → ⟦ a ⟧)
  eval id          c = c
  eval (m ∘ m₁)    c = eval m (eval m₁ c)
  eval fst         c = proj₁ c
  eval snd         c = proj₂ c
  eval (pair m m₁) c = eval m c , eval m₁ c
  eval unit        c = tt
  eval (curry m)   c = λ z → eval m (c , z)
  eval apply       c = proj₁ c (proj₂ c)

  -- normalize a term to normal form
  norm : ∀{a c} → Hom c a → Nf c a
  norm m = reify (eval m (reflect _))

  -- quote a normal form back to term
  q : ∀{c a} → Nf c a → Hom c a
  q unit        = unit
  q (abs n)     = curry (q n)
  q (pair n n₁) = pair (q n) (q n₁)

open NBE

open import Relation.Binary.PropositionalEquality

module Lemmas where

  uniq-abs : ∀ {b c a : Ty} → {f g : Nf (c * a) b} →
    f ≡ g → abs f ≡ abs g
  uniq-abs refl = refl

  uniq-pair : ∀ {b c a : Ty} → {f f' : Nf c a} {g g' : Nf c b} →
    f ≡ f' → g ≡ g' → _≡_ {A = Nf c (a * b)} (pair f g) (pair f' g')
  uniq-pair refl refl = refl

  eta-fun : {a b c : Ty} → (f : Hom c (a ⇒ b)) → f ~ curry (uncurry f)
  eta-fun f =
    eq-trans
      (eq-sym id-l)
      (eq-trans
        (eq-comp (eq-sym curry-apply) eq-refl)
        curry-comp)

  eta-pair : {a b c : Ty} → (f : Hom c (a * b)) → f ~ pair (fst ∘ f) (snd ∘ f)
  eta-pair f =
    eq-trans
      (eq-sym id-l)
      (eq-trans
        (eq-comp id-pair eq-refl)
       pair-comp)

open Lemmas


-- a term is (beta) equivalent to the quotation of its normal form
stable : {a c : Ty} → (f : Hom c a) → f ~ q (norm f)
stable {𝟏} _      =
  unit
stable {_ ⇒ _} f =
  eq-trans
    (eta-fun f)
    (eq-curry (stable (uncurry f)))
stable {_ * _} f =
  eq-trans
    (eta-pair f)
    (eq-pair (stable (fst ∘ f)) (stable (snd ∘ f)))


-- the normal forms of any two terms of the same type are (syntactically) equivalent
-- this is stronger than soundness of normalization (f ~ g → norm f ≡ norm g)
coherent-nf  : {a c : Ty} → (f g : Hom c a) → norm f ≡ norm g
coherent-nf {𝟏}      f g =
  refl
coherent-nf {_ ⇒ _} f  g =
  uniq-abs (coherent-nf (uncurry f) (uncurry g))
coherent-nf {_ * _} f  g =
  uniq-pair (coherent-nf (fst ∘ g) (fst ∘ g)) (coherent-nf (snd ∘ g) (snd ∘ g))


-- completeness of normal forms
-- i.e., (syntactically) equivalent normal forms are (beta) equivalent when quoted 
complete : ∀ {c a : Ty} → {f g : Nf c a} → f ≡ g → q f ~ q g
complete refl = eq-refl


-- coherence property: any two terms of the same type are equal
coherence : {a c : Ty} → (f g : Hom c a) → f ~ g
coherence f g =
  eq-trans
    (stable f)
    (eq-trans
      (complete (coherent-nf f g))
      (eq-sym (stable g)))
