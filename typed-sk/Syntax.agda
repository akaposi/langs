{-# OPTIONS --cubical #-}
-- {-# OPTIONS --allow-unsolved-metas #-} 

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)

module typed-sk.Syntax where

infixr 5 _⇒_
infixl 5 _·_ 

data Ty : Type 

data Tm : Ty → Type
    
data Ty where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty

caseTy : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → Ty → A
caseTy a0 aS ι = a0
caseTy a0 aS (ty ⇒ ty₁) = aS

ιnot⇒ : ∀ {u}{v} → ¬ (ι ≡ u ⇒ v)
ιnot⇒ eq = subst (caseTy Ty ⊥) eq ι

⇒notι : ∀ {u}{v} → ¬ (u ⇒ v ≡ ι)
⇒notι eq = subst (caseTy ⊥ Ty) eq ι

inj⇒₁ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → u ≡ u'
inj⇒₁ e = cong (λ { (u ⇒ v) → u ; _ → ι } ) e
inj⇒₂ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → v ≡ v'
inj⇒₂ e = cong (λ { (u ⇒ v) → v ; _ → ι } ) e

discreteTy : (u v : Ty) → Dec (u ≡ v)
discreteTy ι ι = yes refl
discreteTy ι (v ⇒ v₁) = no (λ p → ιnot⇒ p)
discreteTy (u ⇒ u₁) ι = no λ p → ⇒notι p
discreteTy (u ⇒ u₁) (v ⇒ v₁) with discreteTy u v | discreteTy u₁ v₁
... | yes p | yes p₁ = yes λ i → p i ⇒ (p₁ i)
... | yes p | no ¬p = no λ where x → ¬p (inj⇒₂ x)
... | no ¬p | yes p = no λ where x → ¬p (inj⇒₁ x)
... | no ¬p | no ¬p₁ = no λ where x → ¬p (inj⇒₁ x)

isTySet : isSet Ty 
isTySet = Discrete→isSet discreteTy

⇒-cong : ∀{A₀ A₁ B₀ B₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → A₀ ⇒ B₀ ≡ A₁ ⇒ B₁
⇒-cong a b = λ i → a i ⇒ b i

⇒-inj₁ : ∀{A₀ A₁ B₀ B₁} → A₀ ⇒ B₀ ≡ A₁ ⇒ B₁ → A₀ ≡ A₁
⇒-inj₁ e = cong (λ { (A₀ ⇒ B₀) → A₀ ; _ → ι } ) e

⇒-inj₂ : ∀{A₀ A₁ B₀ B₁} → A₀ ⇒ B₀ ≡ A₁ ⇒ B₁ → B₀ ≡ B₁
⇒-inj₂ e = cong (λ { (A₀ ⇒ B₀) → B₀ ; _ → ι } ) e

data Tm where
  TmSet : ∀{A} → isSet (Tm A)
  _·_ : ∀{A B} → Tm (A ⇒ B) → Tm A → Tm B
  K   : ∀{A B} → Tm (A ⇒ B ⇒ A)
  S   : ∀{A B C} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  Kβ  : ∀{A B}(t : Tm A)(u : Tm B) → K · t · u ≡ t
  Sβ  : ∀{A B C}(t : Tm (A ⇒ B ⇒ C))(u : Tm (A ⇒ B))(v : Tm A) → S · t · u · v ≡ t · v · (u · v)
 
·-cong : ∀{A B}{B₀ B₁ : Tm (A ⇒ B)}{A₀ A₁ : Tm A} → B₀ ≡ B₁ → A₀ ≡ A₁ → B₀ · A₀ ≡  B₁ · A₁
·-cong a b = λ i → (a i) · (b i)

-- ·-inj₁ : ∀{A B}{B₀ B₁ : Tm (A ⇒ B)}{A₀ A₁ : Tm A} → B₀ · A₀ ≡  B₁ · A₁ → B₀ ≡ B₁
-- ·-inj₁ e  =  cong (λ { (B₀ · A₀) → {!   !} ; _ → {!   !} } ) e

-- ·-inj₂ : ∀{A B}{B₀ B₁ : Tm (A ⇒ B)}{A₀ A₁ : Tm A} → B₀ · A₀ ≡  B₁ · A₁ → A₀ ≡ A₁
-- ·-inj₂ e = {!   !}

-- ·-inj₃ : ∀{A B A₁}{B₀ B₁ : Tm (A ⇒ B)}{A₀ A₁ : Tm A} → B₀ · A₀ ≡  B₁ · A₁ → ?
-- ·-inj₃ e = {!   !}