{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import stlc-minimal.Syntax as I
import stlc-minimal.DepModel as Mod
open import stlc-minimal.InitialModel
module stlc-minimal.canon where
  
D : Mod.DepModel InStrict 
Mod.DepModel.Con∙ D Γ = Sub ◆ Γ → hSet lzero
Mod.DepModel.Sub∙ D {Δ} {Γ} Δ∙  Γ∙ γ = ∀{δ◆} → fst (Δ∙ δ◆) → fst (Γ∙ (_∘_ {Δ}{Γ} γ δ◆)) 
Mod.DepModel.SubSet∙ D = {!   !} --γ∙ δ∙ θ* y i j {δ◆} t = {!  (θ* j)  !}
Mod.DepModel._∘∙_ D  {γˢ = γ} {δˢ = δ} {Γ} γ∙ δ∙ θ*  = subst (λ x → fst (Γ x)) (assoc _ _ _ ) (γ∙ (δ∙ θ*)) 
Mod.DepModel.assoc∙ D γ δ θ = λ i x → {!   !}
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
Mod.DepModel.◆∙ D = λ _ → (Unit , λ tt tt e e' → refl)
Mod.DepModel.ε∙ D = _
Mod.DepModel.ε-∘∙ D = {!   !}
Mod.DepModel.◆-η∙ D = {!   !}
Mod.DepModel._⇒∙_ D = {!   !}
Mod.DepModel.app∙ D = {!   !}
Mod.DepModel.app-[]∙ D = {!   !}
Mod.DepModel.lam∙ D = {!   !}
Mod.DepModel.lam-[]∙ D = {!   !}
Mod.DepModel.⇒-β∙ D = {!   !}
Mod.DepModel.⇒-η∙ D = {!   !}
Mod.DepModel.ι∙ D =  {!   !}    