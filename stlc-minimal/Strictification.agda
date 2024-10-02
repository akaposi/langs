{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import stlc-minimal.Syntax as I
import stlc-minimal.DepModel as M

module stlc-minimal.Strictification where

Str : M.DepModel 
M.DepModel.Con Str = λ x → Unit
M.DepModel.Sub Str tt tt Γ = Unit
M.DepModel.SubSet Str = λ x y x₁ y₁ i i₁ → tt
M.DepModel._∘_ Str tt tt = tt
M.DepModel.assoc Str γ δ θ = refl
M.DepModel.id Str = tt
M.DepModel.idr Str tt = refl
M.DepModel.idl Str tt = refl
M.DepModel.Ty Str = λ x → Unit
M.DepModel.Tm Str {Γ} {A} _ _ t = ∀{Δ} → (γ : Sub Δ Γ) → singl (t [ γ ]) 
M.DepModel.TmSet Str = isSetImplicitΠ λ c → isSetΠ (λ Γ → isContr→isOfHLevel 2 (isContrSingl _)) 
M.DepModel._[_] Str {aˢ = aˢ} {γˢ = γˢ} f tt = λ γ → ((aˢ [ γˢ ]) [ γ ]) , refl
M.DepModel.[]-∘ Str {aˢ = aˢ} {γˢ = γˢ} {δˢ = δˢ} a tt tt = λ i γ → ((([]-∘ aˢ γˢ δˢ) i) [ γ ]) , refl
M.DepModel.[]-id Str {aˢ = aˢ} a = λ i γ → ((cong (_[ γ ]) ([]-id aˢ)) ∙ (snd (a γ))) i ,  {!   !} --isProp→PathP (λ j →  TmSet ([]-id aˢ i [ γ ])   (((λ i₁ → []-id aˢ i₁ [ γ ]) ∙ snd (a γ)) i)) {!  !} {!   !} i  
M.DepModel._▸_ Str tt tt = tt
M.DepModel.p Str = tt
M.DepModel.q Str {Γˢ} {Aˢ} γ = (q [ γ ]) , refl
M.DepModel._,_ Str tt f = tt
M.DepModel.,-∘ Str γ a δ = refl
M.DepModel.▸-β₁ Str γ a = refl
M.DepModel.▸-β₂ Str {γˢ} {Γˢ} {δˢ} {aˢ} {aˢ'} tt a i γ = ((cong (_[ γ ]) (▸-β₂ δˢ aˢ')) ∙ (snd (a γ))) i , λ j → {!   !}
M.DepModel.▸-η Str = refl
M.DepModel.◆ Str = tt
M.DepModel.ε Str = tt
M.DepModel.ε-∘ Str tt = refl
M.DepModel.◆-η Str = refl
M.DepModel._⇒_ Str tt tt = tt
M.DepModel.app Str {Γˢ} {t} {t'} {fˢ} {aˢ} f a γ = app (fˢ [ γ ]) (aˢ [ γ ]) ,  (app-[] fˢ aˢ γ)
M.DepModel.app-[] Str = {!   !}
M.DepModel.lam Str = {!   !}
M.DepModel.lam-[] Str = {!   !}
M.DepModel.⇒-β Str = {!   !}
M.DepModel.⇒-η Str = {!   !}
M.DepModel.ι Str = tt  