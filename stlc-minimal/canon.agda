{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import stlc-minimal.Syntax as I
import stlc-minimal.DepModel as Mod
open import stlc-minimal.InitialModel
open import Cubical.Foundations.Transport

open import stlc-minimal.Lib

-- transport (λ z → fst (Γ (assoc γˢ δˢ θˢ z ∘ δ◆₁)))
--       (subst (λ x₁ → fst (Γ x₁)) (assoc γˢ (δˢ ∘ θˢ) δ◆₁)
--        (γ (subst (λ x₁ → fst (Δ x₁)) (assoc δˢ θˢ δ◆₁) (δ (θ x)))))
-- subst-ass : ∀ {Γ Δ} → subst (λ x₁ → fst (Γ x₁)) e1 (γ (subst (λ x₁ → fst (Δ x₁)) e2 ?)) ≡ ?
--     -- γ : {δ◆ : Sub ◆ γˢ.Δˢ} → fst (Δ δ◆) → fst (Γ (γˢ ∘ δ◆))

open import stlc-minimal.DepModel

module stlc-minimal.canon where

open DepModel
  
D : DepModel InStrict 
D .Con∙ Γ = Σ (hSet lzero) λ Γ* → fst Γ* → Sub ◆ Γ
D .Sub∙ {Δ} {Γ} ((Δ* , _) , πΔ) ((Γ* , _) , πΓ) γ = Σ (Δ* → Γ*) λ γ* → (δ* : Δ*) → πΓ (γ* δ*) ≡ γ ∘ πΔ δ*
D .SubSet∙ = {!   !} --γ∙ δ∙ θ* y i j {δ◆} t = {!  (θ* j)  !}
D ._∘∙_ {γˢ = γ} {δˢ = δ} {Γ} γ∙ δ∙ = {!!}
D .assoc∙ = {!!}
D .id∙ = {!!}
D .idr∙ = {!!}
D .idl∙ = {!!}

D .Ty∙ A = Σ (hSet lzero) λ A* → fst A* → Tm ◆ A
D .Tm∙ {Γ} {A} ((Γ* , _) , πΓ) ((A* , _) , πA) a = Σ (Γ* → A*) λ a* → (γ* : Γ*) → πA (a* γ*) ≡ a [ πΓ γ* ]
D .TmSet∙  = {!   !} 
D ._[_]∙ {aˢ = aˢ}{γˢ = γˢ}{A = A} γ δ = {!!}
D .[]-∘∙ = {!   !}
D .[]-id∙ = {!   !}
D ._▸∙_ = {!   !}
D .p∙ = {!   !}
D .q∙ = {!   !}
D ._,∙_ = {!   !}
D .,-∘∙ = {!   !}
D .▸-β₁∙ = {!   !}
D .▸-β₂∙ = {!   !}
D .▸-η∙ = {!   !}
D .◆∙ = {!!}
D .ε∙ = {!!}
D .ε-∘∙ = {!   !}
D .◆-η∙ = {!   !}
D ._⇒∙_ = {!   !}
D .app∙ = {!   !}
D .app-[]∙ = {!   !}
D .lam∙ = {!   !}
D .lam-[]∙ = {!   !}
D .⇒-β∙ = {!   !}
D .⇒-η∙ = {!   !}
D .ι∙ =  {!   !}     
