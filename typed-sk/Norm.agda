{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude

import typed-sk.Syntax as I


module typed-sk.Norm where

_~ : ∀{ℓ ℓ'}{A : Set ℓ}(B : A → Set ℓ'){a₀ a₁ : A}(a₀₁ : a₀ ≡ a₁) → B a₀ → B a₁ → Type ℓ'
(B ~) a₀₁ b₀ b₁ = PathP (λ i → B (a₀₁ i)) b₀ b₁

record DepModel {i j : Level} : Set (lsuc (i ⊔ j)) where
  infixr 5 _⇒∙_
  infixl 5 _$∙_

  field
    Ty∙  : I.Ty → Set i
    ι∙   : Ty∙ I.ι
    _⇒∙_ : ∀{A B} → Ty∙ A → Ty∙ B → Ty∙ (A I.⇒ B)
    Tm∙  : ∀{A} → Ty∙ A → I.Tm A → Set j 
    TmSet· : ∀{A}{A∙ : Ty∙ A}{u : I.Tm A} → isSet (Tm∙ A∙ u) --?--∀{A} → isSet (Tm A)
    _$∙_ : ∀{A B}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{t : I.Tm (A I.⇒ B)}{u : I.Tm A} →
          Tm∙ (A∙ ⇒∙ B∙) t → Tm∙ A∙ u → Tm∙ B∙ (t I.· u)
    K∙   : ∀{A B}{A∙ : Ty∙ A}{B∙ : Ty∙ B} → Tm∙ (A∙ ⇒∙ B∙ ⇒∙ A∙) I.K
    S∙   : ∀{A B C}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{C∙ : Ty∙ C} →
          Tm∙ ((A∙ ⇒∙ B∙ ⇒∙ C∙) ⇒∙ (A∙ ⇒∙ B∙) ⇒∙ A∙ ⇒∙ C∙) I.S
    Kβ∙  : ∀{A B}{A∙ : Ty∙ A}{B∙ : Ty∙ B}(t : I.Tm A)(u : I.Tm B){t∙ : Tm∙ A∙ t}{u∙ : Tm∙ B∙ u} → ((Tm∙ A∙) ~) (I.Kβ t u) (K∙ $∙ t∙ $∙ u∙) t∙ 
    Sβ∙  : ∀{A B C}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{C∙ : Ty∙ C}(t : I.Tm (A I.⇒ B I.⇒ C))(u : I.Tm (A I.⇒ B))(v : I.Tm A){t∙ : Tm∙ (A∙ ⇒∙ B∙ ⇒∙ C∙) t}{u∙ : Tm∙ (A∙ ⇒∙ B∙) u}{v∙ : Tm∙ A∙ v} →
          ((Tm∙ C∙) ~) (I.Sβ t u v) (S∙ $∙ t∙ $∙ u∙ $∙ v∙) ((t∙ $∙ v∙) $∙ (u∙ $∙ v∙))

  ⟦_⟧T : (A : I.Ty) → Ty∙ A
  ⟦ I.ι ⟧T = ι∙
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒∙ ⟦ B ⟧T
  
  ⟦_⟧t :  ∀{A} → (t : I.Tm A) → Tm∙ ⟦ A ⟧T t 
  ⟦ I.TmSet {A} t t' e e' i j ⟧t = {!   !} --TmSet· {A}  {! ⟦ t ⟧t!} {!   !} {!   !} {!   !} i j -- TmSet ⟦ t ⟧t ⟦ t' ⟧t (cong ⟦_⟧t e) (cong ⟦_⟧t e') i j
  ⟦ t I.· u ⟧t = ⟦ t ⟧t $∙ ⟦ u ⟧t
  ⟦ I.K ⟧t = K∙
  ⟦ I.S ⟧t = S∙
  ⟦ I.Kβ {A} {B} u f i ⟧t = Kβ∙ {A} {B} {⟦ A ⟧T} {⟦ B ⟧T} u f {⟦ u ⟧t} {⟦ f ⟧t} i 
  ⟦ I.Sβ {A} {B} {C} f g u i ⟧t = Sβ∙ {A} {B} {C} {⟦ A ⟧T} {⟦ B ⟧T} {⟦ C ⟧T} f g u {⟦ f ⟧t} {⟦ g ⟧t} {⟦ u ⟧t} i


data Nf : (A : I.Ty) → I.Tm A → Set where
  K₀ : ∀{A B} → Nf (A I.Ty.⇒ B I.Ty.⇒ A) I.K
  K₁ : ∀{A B t} → Nf A t → Nf (B I.Ty.⇒ A) (I.K I.· t)
  S₀ : ∀{A B C} → Nf ((A I.Ty.⇒ B I.Ty.⇒ C) I.Ty.⇒ (A I.Ty.⇒ B) I.Ty.⇒ A I.Ty.⇒ C) I.S
  S₁ : ∀{A B C t} → Nf (A I.Ty.⇒ B I.Ty.⇒ C) t → Nf ((A I.Ty.⇒ B) I.Ty.⇒ A I.Ty.⇒ C) (I.S I.· t)
  S₂ : ∀{A B C t u} → Nf (A I.Ty.⇒ B I.Ty.⇒ C) t → Nf (A I.Ty.⇒ B) u → Nf (A I.Ty.⇒ C) (I.S I.· t I.· u)

-- Norm : DepModel
-- Norm = {!   !}   