{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude

import typed-sk.Syntax as I

module typed-sk.Model where

record Model {i j} : Set (lsuc (i ⊔ j)) where
  infixr 5 _⇒_
  infixl 5 _·_

  field
    Ty  : Type i
    ι   : Ty
    _⇒_ : Ty → Ty → Ty
    Tm  : Ty → Type j
    TmSet : ∀{A} → isSet (Tm A)
    _·_ : ∀{A B}    → Tm (A ⇒ B) → Tm A → Tm B
    K   : ∀{A B}    → Tm (A ⇒ B ⇒ A)
    S   : ∀{A B C}  → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    Kβ  : ∀{A B}(t : Tm A)(u : Tm B) → K · t · u ≡ t
    Sβ  : ∀{A B C}(t : Tm (A ⇒ B ⇒ C))(u : Tm (A ⇒ B))(v : Tm A) →
          S · t · u · v ≡ t · v · (u · v)

  ⟦_⟧T : I.Ty → Ty
  ⟦ I.ι ⟧T = ι
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T

  ⟦_⟧t  : ∀{A} → I.Tm A → Tm ⟦ A ⟧T 
  ⟦ I.TmSet {A} t t' e e' i j ⟧t = TmSet ⟦ t ⟧t ⟦ t' ⟧t (cong ⟦_⟧t e) (cong ⟦_⟧t e') i j
  ⟦ t I.· u ⟧t = ⟦ t ⟧t · ⟦ u ⟧t
  ⟦ I.K ⟧t = K
  ⟦ I.S ⟧t = S
  ⟦ I.Kβ u f i ⟧t = Kβ ⟦ u ⟧t ⟦ f ⟧t i
  ⟦ I.Sβ f g u i ⟧t = Sβ ⟦ f ⟧t  ⟦ g ⟧t ⟦ u ⟧t i

