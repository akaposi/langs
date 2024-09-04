{-# OPTIONS --cubical #-}
-- {-# OPTIONS --allow-unsolved-metas #-} 

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)

module stlc-minimal.Syntax where


data Ty : Type 

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


infixl 4 _▸_
data Con : Type where
  _▸_ : Con → Ty → Con
  ◆ : Con