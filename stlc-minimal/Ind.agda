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

module _ (S : DepModel InStrict {ℓ}{ℓ'}) where
  module S = DepModel S

  ⟦_⟧ : DepModel InStrict → DepModel In
  DepModel.Con∙ ⟦ S ⟧ = S.Con∙
  DepModel.Sub∙ ⟦ S ⟧ = S.Sub∙
  DepModel.SubSet∙ ⟦ S ⟧ = S.SubSet∙
  DepModel._∘∙_ ⟦ S ⟧ = S._∘∙_
  DepModel.assoc∙ ⟦ S ⟧ = S.assoc∙
  DepModel.id∙ ⟦ S ⟧ = S.id∙
  DepModel.idr∙ ⟦ S ⟧ = S.idr∙
  DepModel.idl∙ ⟦ S ⟧ = S.idl∙
  DepModel.Ty∙ ⟦ S ⟧ = S.Ty∙
  DepModel.Tm∙ ⟦ S ⟧ = S.Tm∙
  DepModel.TmSet∙ ⟦ S ⟧ = S.TmSet∙    -- I.[]-id aˢ i ≡ aˢ I.[ I.id ]  --I.Tm aˢ.Γˢ aˢ.Aˢ
  DepModel._[_]∙ ⟦ S ⟧ {aˢ = aˢ}{γˢ = γˢ} {Δ = Δ}{A = A} t γ = subst (S.Tm∙ Δ A) (I._[_]= aˢ γˢ) (S._[_]∙ t γ)    -- subst (S.Tm∙ Θ A) (I._[_]=) (S.[]-∘∙ a γ δ i) 
  DepModel.[]-∘∙ ⟦ S ⟧ {Γ}{A}{aˢ}{Δ}{γˢ}{Θ}{δˢ}{Γ∙}{Δ∙}{Θ∙}{A∙} a γ δ = {!  !}  -- i → {! I.[]-∘ aˢ γˢ δˢ  !} --{!  subst (λ x → S.Tm∙ Θ A x) ?  (S.[]-∘∙ a  γ δ i)!}
    -- let U = S.Tm∙ Θ∙ A∙                       --transport-filler'' (λ i → S.Tm∙ Γ A (I.[]-id aˢ i))
                                  -- toPathP {! S.[]-id∙ a  !} 
  DepModel.[]-id∙ ⟦ S ⟧ {aˢ = aˢ}{Γ = Γ}{A = A} a =  toPathP (sym (substComposite (S.Tm∙ Γ A) (aˢ I.[ I.id ]=) (I.[]-id aˢ) (a S.[ S.id∙ ]∙)) ∙ {!  S.[]-id∙ a !}) --(sym(substComposite (S.Tm∙ Γ A) (aˢ I.[ I.id ]=) (I.[]-id aˢ) (a S.[ S.id∙ ]∙))  ∙ fromPathP (S.[]-id∙ a)) 
  DepModel._▸∙_ ⟦ S ⟧ = S._▸∙_ 
  DepModel.p∙ ⟦ S ⟧ = S.p∙
  DepModel.q∙ ⟦ S ⟧ = S.q∙
  DepModel._,∙_ ⟦ S ⟧ = S._,∙_                          --toPathP {!  S.,-∘∙ γ a δ !} 
  DepModel.,-∘∙ ⟦ S ⟧ {Γ}{Δ}{γˢ}{A}{aˢ}{Θ}{δˢ}{Γ∙}{Δ∙}{Θ∙}{A∙} γ a δ = {!  S.,-∘∙ γ a δ !} -- toPathP {!  sym (substComposite (S.Sub∙ Θ∙ (Γ∙ S.▸∙ A∙)) (I.,-∘ γˢ aˢ δˢ) (λ i₁ → γˢ I.∘ δˢ I., (aˢ I.[ δˢ ]=) (~ i₁)) ?) !} --{!   ∙ ? !} -- toPathP {!  substComposite  (λ i → S.Sub∙ Θ (Γ S.▸∙ A) (I.,-∘ γˢ aˢ δˢ i))!} -- S.,-∘∙  γ a δ 
  DepModel.▸-β₁∙ ⟦ S ⟧ = S.▸-β₁∙  
  DepModel.▸-β₂∙ ⟦ S ⟧ {Γ}{Δ}{γˢ}{A}{aˢ}{Γ∙}{Δ∙}{A∙} γ a = substRefl {B = (S.Tm∙ Δ∙ A∙) } (S.q∙ S.[ γ S.,∙ a ]∙) ◁ S.▸-β₂∙ γ a
  DepModel.▸-η∙ ⟦ S ⟧ = S.▸-η∙  
  DepModel.◆∙ ⟦ S ⟧ = S.◆∙
  DepModel.ε∙ ⟦ S ⟧ = S.ε∙
  DepModel.ε-∘∙ ⟦ S ⟧ = S.ε-∘∙
  DepModel.◆-η∙ ⟦ S ⟧ = S.◆-η∙
  DepModel._⇒∙_ ⟦ S ⟧ = S._⇒∙_
  DepModel.app∙ ⟦ S ⟧ = S.app∙
  DepModel.app-[]∙ ⟦ S ⟧ f a γ = {!  S.app-[]∙ f a γ  !}
  DepModel.lam∙ ⟦ S ⟧ = S.lam∙
  DepModel.lam-[]∙ ⟦ S ⟧ b γ = {! S.lam-[]∙ b γ   !}
  DepModel.⇒-β∙ ⟦ S ⟧ {A}{Γ}{B}{bˢ}{aˢ}{Γ∙}{B∙}{A∙} b a = toPathP {!substComposite  (S.Tm∙ Γ∙ A∙) (I.⇒-β bˢ aˢ)  (λ i₁ → (bˢ I.[ I.id I., aˢ ]=) (~ i₁))  (S.app∙ (S.lam∙ b) a)!} --toPathP {!  substComposite (S.Tm∙ Γ B) !}
  DepModel.⇒-η∙ ⟦ S ⟧ f = {!  S.⇒-η∙ f !}
  DepModel.ι∙ ⟦ S ⟧ = S.ι∙
    --  PathP
    --   (λ i →
    --      S.Tm∙ Γ B
    --      ((I.⇒-β bˢ aˢ ∙ (λ i₁ → (bˢ I.[ I.id I., aˢ ]=) (~ i₁))) i))
    --   (S.app∙ (S.lam∙ b) a) (b S.[ S.id∙ S.,∙ a ]∙)