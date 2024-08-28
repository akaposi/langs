{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

module typed-sk.Syntax where

infixr 5 _⇒_
infixl 5 _·_ 

data Ty : Type 

data Tm : Ty → Type
    
data Ty where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty

data Tm where
  TmSet : ∀{A} → isSet (Tm A)
  _·_ : ∀{A B} → Tm (A ⇒ B) → Tm A → Tm B
  K   : ∀{A B} → Tm (A ⇒ B ⇒ A)
  S   : ∀{A B C} → Tm ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  Kβ  : ∀{A B}(t : Tm A)(u : Tm B) → K · t · u ≡ t
  Sβ  : ∀{A B C}(t : Tm (A ⇒ B ⇒ C))(u : Tm (A ⇒ B))(v : Tm A) → S · t · u · v ≡ t · v · (u · v)

