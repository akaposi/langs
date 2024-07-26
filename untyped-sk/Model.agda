{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude

import untyped-sk.Syntax as I

module untyped-sk.Model where

record Model {ℓ} : Set (lsuc ℓ) where
  infixl 5 _·_ 
  field
    Tm    : Type ℓ
    TmSet : isSet Tm
    _·_   : Tm → Tm → Tm
    K S   : Tm
    Kβ    : ∀{u f} → K · u · f ≡ u
    Sβ    : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)
    
  ⟦_⟧ : I.Tm → Tm
  ⟦ I.TmSet t t' e e' i j ⟧ = TmSet ⟦ t ⟧ ⟦ t' ⟧ (cong ⟦_⟧ e) (cong ⟦_⟧ e') i j
  ⟦ t I.· u ⟧ = ⟦ t ⟧ · ⟦ u ⟧
  ⟦ I.K ⟧ = K
  ⟦ I.S ⟧ = S
  ⟦ I.Kβ {u}{f} i ⟧ = Kβ {⟦ u ⟧}{⟦ f ⟧} i
  ⟦ I.Sβ {f}{g}{u} i ⟧ = Sβ {⟦ f ⟧}{⟦ g ⟧}{⟦ u ⟧} i

  I' : Tm
  I' = S · K · K
  Iβ : ∀{u} → I' · u ≡ u
  Iβ {u} =
      (S · K · K · u)
              ≡⟨ Sβ ⟩ 
      (K · u · (K · u))
              ≡⟨ Kβ ⟩ 
      refl

  B : Tm
  B = S · (K · S) · K
  Bβ : ∀{f g u} → B · f · g · u ≡ f · (g · u)
  Bβ {f}{g}{u} = 
      (S · (K · S) · K · f · g · u)
              ≡⟨ cong (λ z → z · g · u) Sβ ⟩ 
      (K · S · f · (K · f) · g · u)
              ≡⟨ cong (λ z → z · (K · f) · g · u) Kβ ⟩ 
      (S · (K · f) · g · u)
              ≡⟨ Sβ ⟩ 
      (K · f · u · (g · u))
              ≡⟨ cong (λ z → z · (g · u)) Kβ ⟩ 
      refl

  C : Tm
  C = S · (S · (K · B) · S) · (K · K)
  Cβ : ∀{f g u} → C · f · u · g ≡ f · g · u
  Cβ {f}{g}{u} = 
      (S · (S · (K · B) · S) · (K · K) · f · u · g)
              ≡⟨ cong (λ z → z · u · g) Sβ ⟩ 
      (S · (K · B) · S · f · (K · K · f) · u · g)
              ≡⟨ cong (λ z → z · ((K · K) · f) · u · g) Sβ ⟩ 
      (K · B · f · (S · f) · (K · K · f) · u · g)
              ≡⟨ cong (λ z → z · (S · f) · (K · K · f) · u · g) Kβ ⟩ 
      (B · (S · f) · (K · K · f) · u · g)
              ≡⟨ cong (λ z → z · g) Bβ ⟩ 
      (S · f · (K · K · f · u) · g)
              ≡⟨ Sβ ⟩ 
      (f · g · (K · K · f · u · g))
              ≡⟨ cong (λ z → f · g · (z · u · g)) Kβ ⟩ 
      (f · g · (K · u · g))
              ≡⟨ cong (λ z → f · g · z) Kβ ⟩ 
      refl
