{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

module untyped-sk.Syntax where

infixl 5 _·_ 

data Tm : Type where
  TmSet : isSet Tm
  _·_   : Tm → Tm → Tm
  K S   : Tm
  Kβ    : ∀{u f} → K · u · f ≡ u
  Sβ    : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)

