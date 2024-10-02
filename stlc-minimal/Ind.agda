{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Path
-- open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)


open import stlc-minimal.DepModel 

module stlc-minimal.Ind (M : DepModel) where

import stlc-minimal.Syntax as I
private module M = DepModel M
private variable
  Γ Δ : I.Con
  A : I.Ty


--Recursor 

⟦_⟧Tᵢ : ∀ A → M.Ty A
⟦ I.ι ⟧Tᵢ = M.ι
⟦ A I.⇒ B ⟧Tᵢ = ⟦ A ⟧Tᵢ M.⇒ ⟦ B ⟧Tᵢ


⟦_⟧Cᵢ : ∀ Γ → M.Con Γ
⟦ Γ I.▸ A ⟧Cᵢ = ⟦ Γ ⟧Cᵢ M.▸ ⟦ A ⟧Tᵢ
⟦ I.◆ ⟧Cᵢ = M.◆

⟦_⟧Sᵢ : ∀ γ → M.Sub (⟦ Δ ⟧Cᵢ) (⟦ Γ ⟧Cᵢ) γ
⟦_⟧tᵢ : ∀ a → M.Tm (⟦ Γ ⟧Cᵢ) (⟦ A ⟧Tᵢ) a


⟦ I.SubSet γ₁ γ₂ p q i j ⟧Sᵢ =  isSet→SquareP  {A = λ i j → M.Sub _ _ (I.SubSet _ _ _ _ i j)} (λ i₁ j₁ → M.SubSet) (λ k → ⟦ (p k) ⟧Sᵢ) (λ k → ⟦ (q k) ⟧Sᵢ) refl refl i j
⟦ γ I.∘ δ ⟧Sᵢ = ⟦ γ ⟧Sᵢ M.∘ ⟦ δ ⟧Sᵢ
⟦ I.assoc γ δ θ i ⟧Sᵢ = M.assoc ⟦ γ ⟧Sᵢ ⟦ δ ⟧Sᵢ ⟦ θ ⟧Sᵢ i
⟦ I.id ⟧Sᵢ = M.id
⟦ I.idr γ i ⟧Sᵢ = M.idr ⟦ γ ⟧Sᵢ i
⟦ I.idl γ i ⟧Sᵢ = M.idl ⟦ γ ⟧Sᵢ i
⟦ I.p ⟧Sᵢ = M.p
⟦ γ I., a ⟧Sᵢ = ⟦ γ ⟧Sᵢ M., ⟦ a ⟧tᵢ
⟦ I.,-∘ γ a δ i ⟧Sᵢ = M.,-∘ ⟦ γ ⟧Sᵢ ⟦ a ⟧tᵢ ⟦ δ ⟧Sᵢ i
⟦ I.▸-β₁ γ a i ⟧Sᵢ = M.▸-β₁ ⟦ γ ⟧Sᵢ ⟦ a ⟧tᵢ i
⟦ I.▸-η i ⟧Sᵢ = M.▸-η i
⟦ I.ε ⟧Sᵢ = M.ε
⟦ I.ε-∘ γ i ⟧Sᵢ = M.ε-∘ ⟦ γ ⟧Sᵢ i
⟦ I.◆-η i ⟧Sᵢ = M.◆-η i



⟦ I.TmSet γ₁ γ₂ p q i j ⟧tᵢ = isSet→SquareP {A = λ i j → M.Tm _ _ (I.TmSet _ _ _ _ i j)} (λ i₁ j₁ → M.TmSet) (λ k → ⟦ (p k) ⟧tᵢ) (λ k → ⟦ (q k) ⟧tᵢ) refl refl i j
⟦ a I.[ γ ] ⟧tᵢ = ⟦ a ⟧tᵢ M.[ ⟦ γ ⟧Sᵢ ]
⟦ I.[]-∘ a γ δ i ⟧tᵢ = M.[]-∘ ⟦ a ⟧tᵢ ⟦ γ ⟧Sᵢ ⟦ δ ⟧Sᵢ i
⟦ I.[]-id a i ⟧tᵢ = M.[]-id ⟦ a ⟧tᵢ i
⟦ I.q ⟧tᵢ = M.q
⟦ I.▸-β₂ γ a i ⟧tᵢ = M.▸-β₂ ⟦ γ ⟧Sᵢ ⟦ a ⟧tᵢ i
⟦ I.app f a ⟧tᵢ = M.app ⟦ f ⟧tᵢ ⟦ a ⟧tᵢ
⟦ I.app-[] f a γ i ⟧tᵢ = M.app-[] ⟦ f ⟧tᵢ ⟦ a ⟧tᵢ ⟦ γ ⟧Sᵢ i
⟦ I.lam a ⟧tᵢ = M.lam ⟦ a ⟧tᵢ
⟦ I.lam-[] a γ i ⟧tᵢ = M.lam-[] ⟦ a ⟧tᵢ ⟦ γ ⟧Sᵢ i
⟦ I.⇒-β f a i ⟧tᵢ = M.⇒-β ⟦ f ⟧tᵢ ⟦ a ⟧tᵢ i
⟦ I.⇒-η a i ⟧tᵢ = M.⇒-η ⟦ a ⟧tᵢ i

