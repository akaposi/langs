{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)


import stlc-minimal.Syntax as I

module stlc-minimal.DepModel where

private variable
--   n : Nat
  Γˢ Δˢ : I.Con
  γˢ γ₁ˢ γ₂ˢ δˢ θˢ : I.Sub Δˢ Γˢ
  Aˢ Bˢ : I.Ty
  aˢ a₁ˢ a₂ˢ bˢ fˢ tˢ : I.Tm Γˢ Aˢ

record DepModel {ℓ}{ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  no-eta-equality
  field
    Con : I.Con → Type ℓ
    Sub : Con Δˢ → Con Γˢ → I.Sub Δˢ Γˢ → Type ℓ'
    SubSet : ∀ {Δ Γ} → isSet (Sub Δ Γ γˢ)
 
  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : ∀ {Δ Γ} → Sub Δ Γ γ₁ˢ → γ₁ˢ ≡ γ₂ˢ → Sub Δ Γ γ₂ˢ → Type ℓ'
  _≡ˢ[_]_ {_} {_} {_} {_} {Δ} {Γ} γ₁ γ₁ˢ≡γ₂ˢ γ₂ =
    PathP (λ i → Sub Δ Γ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂

  infixl 40 _∘_
  field
    _∘_ : ∀ {Γ Δ Θ} → Sub Δ Γ γˢ → Sub Θ Δ δˢ → Sub Θ Γ (γˢ I.∘ δˢ)
    assoc :
      ∀ {Γ Δ Θ Ξ} (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) (θ : Sub Ξ Θ θˢ) →
      γ ∘ (δ ∘ θ) ≡ˢ[ I.assoc _ _ _ ] γ ∘ δ ∘ θ

    id : {Γ : Con Γˢ} → Sub Γ Γ I.id
    idr : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → γ ∘ id ≡ˢ[ I.idr _ ] γ
    idl : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → id ∘ γ ≡ˢ[ I.idl _ ] γ

  field
    Ty : I.Ty → Type ℓ
    Tm : Con Γˢ → Ty Aˢ → I.Tm Γˢ Aˢ → Type ℓ'
    TmSet : ∀ {Γ A} → isSet (Tm Γ A aˢ)

  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ A} → Tm Γ A a₁ˢ → a₁ˢ ≡ a₂ˢ → Tm Γ A a₂ˢ → Type ℓ'
  _≡ᵗ[_]_ {_} {_} {_} {_} {Γ} {A} a₁ a₁ˢ≡a₂ˢ a₂ =
    PathP (λ i → Tm Γ A (a₁ˢ≡a₂ˢ i)) a₁ a₂

  infixl 40 _[_]
  field
    _[_] : ∀ {Γ Δ A} → Tm Γ A aˢ → Sub Δ Γ γˢ → Tm Δ A (aˢ I.[ γˢ ])
    []-∘ :
      ∀ {Γ Δ Θ A} (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) →
      a [ γ ∘ δ ] ≡ᵗ[ I.[]-∘ _ _ _ ] a [ γ ] [ δ ]
    []-id : ∀ {Γ A} (a : Tm Γ A aˢ) → a [ id ] ≡ᵗ[ I.[]-id _ ] a

  infixl 4 _▸_ _,_
  field
    _▸_ : Con Γˢ → Ty Aˢ → Con (Γˢ I.▸ Aˢ)
    p : {Γ : Con Γˢ} {A : Ty Aˢ} → Sub (Γ ▸ A) Γ I.p
    q : {Γ : Con Γˢ} {A : Ty Aˢ} → Tm (Γ ▸ A) A I.q

    _,_ : ∀ {Γ Δ A} → Sub Δ Γ γˢ → Tm Δ A aˢ → Sub Δ (Γ ▸ A) (γˢ I., aˢ)
    ,-∘ :
      ∀ {Γ Δ Θ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) (δ : Sub Θ Δ δˢ) →
      (γ , a) ∘ δ ≡ˢ[ I.,-∘ _ _ _ ] (γ ∘ δ , a [ δ ])

    ▸-β₁ :
      ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
      p ∘ (γ , a) ≡ˢ[ I.▸-β₁ _ _ ] γ
    ▸-β₂ :
      ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
      q [ γ , a ] ≡ᵗ[ I.▸-β₂ _ _ ] a
    ▸-η : {Γ : Con Γˢ} {A : Ty Aˢ} → (p , q) ≡ˢ[ I.▸-η ] id {Γ = Γ ▸ A}

    ◆ : Con I.◆
    ε : {Γ : Con Γˢ} → Sub Γ ◆ I.ε
    ε-∘ : ∀ {Γ Δ} (γ : Sub Δ Γ γˢ) → ε ∘ γ ≡ˢ[ I.ε-∘ _ ] ε
    ◆-η : ε ≡ˢ[ I.◆-η ] id

  infixl 4 _↑
  _↑ : ∀ {Γ Δ} {A : Ty Aˢ} → Sub Δ Γ γˢ → Sub (Δ ▸ A) (Γ ▸ A) (γˢ I.↑)
  γ ↑ = γ ∘ p , q

  ⟨_⟩ : ∀ {Γ A} → Tm Γ A aˢ → Sub Γ (Γ ▸ A) I.⟨ aˢ ⟩
  ⟨_⟩ = id ,_

  infixr 0 _⇒_
  field
    _⇒_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ I.⇒ Bˢ)
    app : ∀ {Γ A B} → Tm Γ (A ⇒ B) fˢ → Tm Γ A aˢ → Tm Γ B (I.app fˢ aˢ)
    app-[] :
      ∀ {Γ Δ A B} (f : Tm Γ (A ⇒ B) fˢ) (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) →
      app f a [ γ ] ≡ᵗ[ I.app-[] _ _ _ ] app (f [ γ ]) (a [ γ ])

    lam : ∀ {Γ A B} → Tm (Γ ▸ A) B bˢ → Tm Γ (A ⇒ B) (I.lam bˢ)
    lam-[] :
      ∀ {Γ Δ A B} (b : Tm (Γ ▸ A) B bˢ) (γ : Sub Δ Γ γˢ) →
      lam b [ γ ] ≡ᵗ[ I.lam-[] _ _ ] lam (b [ γ ↑ ])

    ⇒-β :
      ∀ {Γ A B} (b : Tm (Γ ▸ A) B bˢ) (a : Tm Γ A aˢ) →
      app (lam b) a ≡ᵗ[ I.⇒-β _ _ ] b [ ⟨ a ⟩ ]
    ⇒-η :
      ∀ {Γ A B} (f : Tm Γ (A ⇒ B) fˢ) → lam (app (f [ p ]) q) ≡ᵗ[ I.⇒-η _ ] f

    ι : Ty I.ι 
