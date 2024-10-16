{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)

open import Cubical.Foundations.Transport

open import stlc-minimal.DepModel 
open import stlc-minimal.InitialModel 

module stlc-minimal.Ind {ℓ}{ℓ'}(D : DepModel In {ℓ}{ℓ'}) where

import stlc-minimal.Syntax as I
private module D = DepModel D

transport-filler'' : ∀ {ℓ} {A B : Type ℓ} (p : B ≡ A) {x : A}{y : A}(e : x ≡ y)
                   → PathP (λ i → p i) (transport (λ i → p (~ i)) x) y
transport-filler'' p e i = transp (λ j → p (i ∨ ~ j)) i (e i)


private variable
  Γ Δ : I.Con
  A : I.Ty

⟦_⟧Tᵢ : ∀ A → D.Ty∙ A
⟦ I.ι ⟧Tᵢ = D.ι∙
⟦ A I.⇒ B ⟧Tᵢ = ⟦ A ⟧Tᵢ D.⇒∙ ⟦ B ⟧Tᵢ

⟦_⟧Cᵢ : ∀ Γ → D.Con∙ Γ
⟦ Γ I.▸ A ⟧Cᵢ = ⟦ Γ ⟧Cᵢ D.▸∙ ⟦ A ⟧Tᵢ
⟦ I.◆ ⟧Cᵢ = D.◆∙

⟦_⟧Sᵢ : ∀ γ → D.Sub∙ (⟦ Δ ⟧Cᵢ) (⟦ Γ ⟧Cᵢ) γ
⟦_⟧tᵢ : ∀ a → D.Tm∙ (⟦ Γ ⟧Cᵢ) (⟦ A ⟧Tᵢ) a

⟦ I.SubSet γ₁ γ₂ p q i j ⟧Sᵢ =  isSet→SquareP  {A = λ i j → D.Sub∙ _ _ (I.SubSet _ _ _ _ i j)} (λ i₁ j₁ → D.SubSet∙) (λ k → ⟦ (p k) ⟧Sᵢ) (λ k → ⟦ (q k) ⟧Sᵢ) refl refl i j
⟦ γ I.∘ δ ⟧Sᵢ = ⟦ γ ⟧Sᵢ D.∘∙ ⟦ δ ⟧Sᵢ
⟦ I.assoc γ δ θ i ⟧Sᵢ = D.assoc∙ ⟦ γ ⟧Sᵢ ⟦ δ ⟧Sᵢ ⟦ θ ⟧Sᵢ i
⟦ I.id ⟧Sᵢ = D.id∙
⟦ I.idr γ i ⟧Sᵢ = D.idr∙ ⟦ γ ⟧Sᵢ i
⟦ I.idl γ i ⟧Sᵢ = D.idl∙ ⟦ γ ⟧Sᵢ i
⟦ I.p ⟧Sᵢ = D.p∙
⟦ γ I., a ⟧Sᵢ = ⟦ γ ⟧Sᵢ D.,∙ ⟦ a ⟧tᵢ
⟦ I.,-∘ γ a δ i ⟧Sᵢ = D.,-∘∙ ⟦ γ ⟧Sᵢ ⟦ a ⟧tᵢ ⟦ δ ⟧Sᵢ i 
⟦ I.▸-β₁ γ a i ⟧Sᵢ = D.▸-β₁∙ ⟦ γ ⟧Sᵢ ⟦ a ⟧tᵢ i
⟦ I.▸-η i ⟧Sᵢ = D.▸-η∙ i
⟦ I.ε ⟧Sᵢ = D.ε∙
⟦ I.ε-∘ γ i ⟧Sᵢ = D.ε-∘∙ ⟦ γ ⟧Sᵢ i
⟦ I.◆-η i ⟧Sᵢ = D.◆-η∙ i

⟦ I.TmSet γ₁ γ₂ p q i j ⟧tᵢ = isSet→SquareP {A = λ i j → D.Tm∙ _ _ (I.TmSet _ _ _ _ i j)} (λ i₁ j₁ → D.TmSet∙) (λ k → ⟦ (p k) ⟧tᵢ) (λ k → ⟦ (q k) ⟧tᵢ) refl refl i j
⟦ a I.[ γ ] ⟧tᵢ = ⟦ a ⟧tᵢ D.[ ⟦ γ ⟧Sᵢ ]∙ 
⟦ I.[]-∘ a γ δ i ⟧tᵢ = D.[]-∘∙ ⟦ a ⟧tᵢ ⟦ γ ⟧Sᵢ ⟦ δ ⟧Sᵢ i
⟦ I.[]-id a i ⟧tᵢ = D.[]-id∙ ⟦ a ⟧tᵢ i
⟦ I.q ⟧tᵢ = D.q∙
⟦ I.▸-β₂ γ a i ⟧tᵢ = D.▸-β₂∙ ⟦ γ ⟧Sᵢ ⟦ a ⟧tᵢ i
⟦ I.app f a ⟧tᵢ = D.app∙ ⟦ f ⟧tᵢ ⟦ a ⟧tᵢ
⟦ I.app-[] f a γ i ⟧tᵢ = D.app-[]∙ ⟦ f ⟧tᵢ ⟦ a ⟧tᵢ ⟦ γ ⟧Sᵢ i
⟦ I.lam a ⟧tᵢ = D.lam∙ ⟦ a ⟧tᵢ
⟦ I.lam-[] a γ i ⟧tᵢ = D.lam-[]∙ ⟦ a ⟧tᵢ ⟦ γ ⟧Sᵢ i
⟦ I.⇒-β f a i ⟧tᵢ = D.⇒-β∙ ⟦ f ⟧tᵢ ⟦ a ⟧tᵢ i
⟦ I.⇒-η a i ⟧tᵢ = D.⇒-η∙ ⟦ a ⟧tᵢ i
