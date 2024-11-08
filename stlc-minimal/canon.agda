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

module stlc-minimal.canon where
  
D : Mod.DepModel InStrict 
Mod.DepModel.Con∙ D Γ = Sub ◆ Γ → hSet lzero
Mod.DepModel.Sub∙ D {Δ} {Γ} Δ∙ Γ∙ γ = ∀{δ◆} → fst (Δ∙ δ◆) → fst (Γ∙ (_∘_ {Δ}{Γ} γ δ◆)) 
Mod.DepModel.SubSet∙ D = {!   !} --γ∙ δ∙ θ* y i j {δ◆} t = {!  (θ* j)  !}
Mod.DepModel._∘∙_ D  {γˢ = γ} {δˢ = δ} {Γ} γ∙ δ∙ θ*  = subst (λ x → fst (Γ x)) (assoc _ _ _ ) (γ∙ (δ∙ θ*)) 
Mod.DepModel.assoc∙ D {γˢ = γˢ}{δˢ = δˢ}{θˢ = θˢ}{Γ = Γ} γ δ θ =  
    implicitFunExt λ {δ◆₁} → funExt λ x → 
    toPathP (sym (substsubst (λ x₁ → fst (Γ x₁)) (assoc γˢ δˢ (θˢ ∘ δ◆₁)) (assoc (γˢ ∘ δˢ) θˢ δ◆₁) {!    !})) 
Mod.DepModel.id∙ D {Γ = Γ} δ◆ = subst (λ x → fst (Γ x)) (sym (idl _)) δ◆
Mod.DepModel.idr∙ D γ = implicitFunExt (λ {δ◆₁} →  funExt (λ x → toPathP {!  !}))
Mod.DepModel.idl∙ D {γˢ = γˢ}{Γ}{Δ} γ = implicitFunExt (λ {δ◆₁} →  funExt (λ x → toPathP {!   !} ))-- ((cong (λ a → transport (λ z → fst (Γ (idl γˢ z ∘ δ◆₁))) a) (substsubst (λ x₁ → fst (Γ x₁))  (λ i → idl (γˢ ∘ δ◆₁) (~ i)) (assoc id γˢ δ◆₁) {!   !})) ∙ {!   !})))
Mod.DepModel.Ty∙ D A = Tm ◆ A → hSet lzero                                                        
Mod.DepModel.Tm∙ D {Γ} {A} Γ∙ A∙ a  = {γₛ : Sub ◆ Γ} → fst (Γ∙ γₛ)  → fst (A∙ (a [ γₛ ]))
Mod.DepModel.TmSet∙ D  = {!   !} 
Mod.DepModel._[_]∙ D {aˢ = aˢ}{γˢ = γˢ}{A = A} γ δ {γₛ} Δ∙ =  subst  (λ y → fst (A (y [ γₛ ]))) (sym (aˢ [ γˢ ]=)) ((subst (λ z → fst (A z)) ([]-∘ aˢ γˢ γₛ)) (γ (δ Δ∙)))  
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