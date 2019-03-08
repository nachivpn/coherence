module NBE where

open import CCC


data Nf (C : Ty) : Ty → Set where
  unit : Nf C 𝟏
  abs  : ∀ {A B} → Nf (C * A) B → Nf C (A ⇒ B)
  pair : ∀ {A B} → Nf C A → Nf C B → Nf C (A * B)

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


open import Function renaming (_∘_ to _∙_) using ()

norm : ∀{a c} → Hom c a → Nf c a
norm m = reify (eval m (reflect _))


open import Relation.Binary.PropositionalEquality

uniq-abs : ∀ {b c a : Ty} → {f g : Nf (c * a) b} →
  f ≡ g → abs f ≡ abs g
uniq-abs refl = refl

uniq-pair : ∀ {b c a : Ty} → {f f' : Nf c a} {g g' : Nf c b} →
  f ≡ f' → g ≡ g' → _≡_ {A = Nf c (a * b)} (pair f g) (pair f' g')
uniq-pair refl refl = refl

uniq  : {a c : Ty} → (f g : Hom c a) → norm f ≡ norm g
uniq {𝟏}      f g = refl
uniq {_ ⇒ _} f g = uniq-abs (uniq (uncurry f) (uncurry g))
uniq {_ * _} f g = uniq-pair (uniq (fst ∘ g) (fst ∘ g)) (uniq (snd ∘ g) (snd ∘ g))

-- quote a normal form back to term
q : ∀{c a} → Nf c a → Hom c a
q unit        = unit
q (abs n)     = curry (q n)
q (pair n n₁) = pair (q n) (q n₁)

eta-fun : {a b c : Ty} → (f : Hom c (a ⇒ b)) → f ~ curry (uncurry f)
eta-fun f = {!!}

eta-pair : {a b c : Ty} → (f : Hom c (a * b)) → f ~ pair (fst ∘ f) (snd ∘ f)
eta-pair f = {!!}

stable : {a c : Ty} → (f : Hom c a) → f ~ q (norm f)
stable {𝟏} _      =
  unit
stable {_ ⇒ _} f =
  eq-trans (eta-fun f) (eq-curry (stable (uncurry f)))
stable {_ * _} f =
  eq-trans (eta-pair f) (eq-pair (stable (fst ∘ f)) (stable (snd ∘ f)))
  
complete : ∀ {c a : Ty} → {f g : Nf c a} → f ≡ g → q f ~ q g
complete refl = eq-refl

-- any two terms of same type are equal
coherence : {a c : Ty} → (f g : Hom c a) → f ~ g
coherence f g =
  eq-trans (stable f) (eq-trans (complete (uniq f g)) (eq-sym (stable g)))
