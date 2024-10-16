{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import stlc-minimal.Syntax as I
import stlc-minimal.DepModel as Mod
open import stlc-minimal.InitialModel
module stlc-minimal.Strictification where
  
D : Mod.DepModel InStrict 
Mod.DepModel.Con∙ D Γ = Sub ◆ Γ → hSet lzero
Mod.DepModel.Sub∙ D {Δˢ} {Γˢ} Δ∙ Γ∙ γ = {! Δ∙  !}
Mod.DepModel.SubSet∙ D = {!   !}
Mod.DepModel._∘∙_ D = {!   !}
Mod.DepModel.assoc∙ D = {!   !}
Mod.DepModel.id∙ D = {!   !}
Mod.DepModel.idr∙ D = {!   !}
Mod.DepModel.idl∙ D = {!   !}
Mod.DepModel.Ty∙ D A = Tm ◆ A → hSet lzero
Mod.DepModel.Tm∙ D {Γ} {A} Γ∙ A∙ a  = {γₛ : Sub ◆ Γ } → fst (Γ∙ γₛ)  → fst (A∙ (a [ γₛ ]))
Mod.DepModel.TmSet∙ D = {!   !}
Mod.DepModel._[_]∙ D = {!   !}
Mod.DepModel.[]-∘∙ D = {!   !}
Mod.DepModel.[]-id∙ D = {!   !}
Mod.DepModel._▸∙_ D = {!   !}
Mod.DepModel.p∙ D = {!   !}
Mod.DepModel.q∙ D = {!   !}
Mod.DepModel._,∙_ D = {!   !}
Mod.DepModel.,-∘∙ D = {!   !}
Mod.DepModel.▸-β₁∙ D = {!   !}
Mod.DepModel.▸-β₂∙ D = {!   !}
Mod.DepModel.▸-η∙ D = {!   !}
Mod.DepModel.◆∙ D = {!   !}
Mod.DepModel.ε∙ D = {!   !}
Mod.DepModel.ε-∘∙ D = {!   !}
Mod.DepModel.◆-η∙ D = {!   !}
Mod.DepModel._⇒∙_ D = {!   !}
Mod.DepModel.app∙ D = {!   !}
Mod.DepModel.app-[]∙ D = {!   !}
Mod.DepModel.lam∙ D = {!   !}
Mod.DepModel.lam-[]∙ D = {!   !}
Mod.DepModel.⇒-β∙ D = {!   !}
Mod.DepModel.⇒-η∙ D = {!   !}
Mod.DepModel.ι∙ D = {!   !}
--  
-- M.DepModel.Con∙ D Γ = Sub ◆ Γ → hSet lzero
-- M.DepModel.Sub∙ D {Δˢ} {Γˢ} Δ∙ Γ∙ γ = {!  !} 
-- M.DepModel.SubSet∙ D = {!   !}
-- M.DepModel._∘∙_ D = {!   !}
-- M.DepModel.assoc∙ D = {!   !}
-- M.DepModel.id∙ D = {!   !}
-- M.DepModel.idr∙ D = {!   !}
-- M.DepModel.idl∙ D = {!   !}
-- M.DepModel.Ty∙ D A = Tm ◆ A → hSet lzero
-- M.DepModel.Tm∙ D {Γ} {A} Γ∙ A∙ a  = {γₛ : Sub ◆ Γ } → fst (Γ∙ γₛ)  → fst (A∙ (a [ γₛ ]))
-- M.DepModel.TmSet∙ D {Γ}{t}{u}{C∙}{t∙}  = {!   !} -- λ {A}{A∙}{u} → snd (fst A∙ u); 
-- M.DepModel._[_]∙ D = {!   !}
-- M.DepModel.[]-∘∙ D = {!   !}
-- M.DepModel.[]-id∙ D = {!   !}
-- M.DepModel._▸∙_ D = {!   !}
-- M.DepModel.p∙ D = {!   !}
-- M.DepModel.q∙ D = {!   !}
-- M.DepModel._,∙_ D = {!   !}
-- M.DepModel.,-∘∙ D = {!   !}
-- M.DepModel.▸-β₁∙ D = {!   !}
-- M.DepModel.▸-β₂∙ D = {!   !}
-- M.DepModel.▸-η∙ D = {!   !}
-- M.DepModel.◆∙ D = {!   !}
-- M.DepModel.ε∙ D = {!   !}
-- M.DepModel.ε-∘∙ D = {!   !}
-- M.DepModel.◆-η∙ D = {!   !}
-- M.DepModel._⇒∙_ D = {!   !}
-- M.DepModel.app∙ D = {!   !}
-- M.DepModel.app-[]∙ D = {!   !}
-- M.DepModel.lam∙ D = {!   !}
-- M.DepModel.lam-[]∙ D = {!   !}
-- M.DepModel.⇒-β∙ D = {!   !}
-- M.DepModel.⇒-η∙ D = {!   !}
-- M.DepModel.ι∙ D = {!   !}

-- D* : M.DepModel
-- D* = {!   !}
-- Str : M.DepModel 
-- M.DepModel.Con Str = λ x → Unit
-- M.DepModel.Sub Str tt tt Γ = Unit
-- M.DepModel.SubSet Str = λ x y x₁ y₁ i i₁ → tt
-- M.DepModel._∘_ Str tt tt = tt
-- M.DepModel.assoc Str γ δ θ = refl
-- M.DepModel.id Str = tt
-- M.DepModel.idr Str tt = refl
-- M.DepModel.idl Str tt = refl
-- M.DepModel.Ty Str = λ x → Unit
-- M.DepModel.Tm Str {Γ} {A} _ _ t = ∀{Δ} → (γ : Sub Δ Γ) → singl (t [ γ ]) 
-- M.DepModel.TmSet Str = isSetImplicitΠ λ c → isSetΠ (λ Γ → isContr→isOfHLevel 2 (isContrSingl _)) 
-- M.DepModel._[_] Str {aˢ = aˢ} {γˢ = γˢ} f tt = λ γ → ((aˢ [ γˢ ]) [ γ ]) , refl
-- M.DepModel.[]-∘ Str {aˢ = aˢ} {γˢ = γˢ} {δˢ = δˢ} a tt tt = λ i γ → ((([]-∘ aˢ γˢ δˢ) i) [ γ ]) , refl
-- M.DepModel.[]-id Str {aˢ = aˢ} a = λ i γ → ((cong (_[ γ ]) ([]-id aˢ)) ∙ (snd (a γ))) i ,  {!   !} --isProp→PathP (λ j →  TmSet ([]-id aˢ i [ γ ])   (((λ i₁ → []-id aˢ i₁ [ γ ]) ∙ snd (a γ)) i)) {!  !} {!   !} i  
-- M.DepModel._▸_ Str tt tt = tt
-- M.DepModel.p Str = tt
-- M.DepModel.q Str {Γˢ} {Aˢ} γ = (q [ γ ]) , refl
-- M.DepModel._,_ Str tt f = tt
-- M.DepModel.,-∘ Str γ a δ = refl
-- M.DepModel.▸-β₁ Str γ a = refl
-- M.DepModel.▸-β₂ Str {γˢ} {Γˢ} {δˢ} {aˢ} {aˢ'} tt a i γ = ((cong (_[ γ ]) (▸-β₂ δˢ aˢ')) ∙ (snd (a γ))) i , λ j → {!   !}
-- M.DepModel.▸-η Str = refl
-- M.DepModel.◆ Str = tt
-- M.DepModel.ε Str = tt
-- M.DepModel.ε-∘ Str tt = refl
-- M.DepModel.◆-η Str = refl
-- M.DepModel._⇒_ Str tt tt = tt
-- M.DepModel.app Str {Γˢ} {t} {t'} {fˢ} {aˢ} f a γ = app (fˢ [ γ ]) (aˢ [ γ ]) ,  (app-[] fˢ aˢ γ)
-- M.DepModel.app-[] Str = {!   !}
-- M.DepModel.lam Str = {!   !}
-- M.DepModel.lam-[] Str = {!   !}
-- M.DepModel.⇒-β Str = {!   !}
-- M.DepModel.⇒-η Str = {!   !}
-- M.DepModel.ι Str = tt    