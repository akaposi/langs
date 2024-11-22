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
D .SubSet∙ {γˢ = γˢ} {Δ = Δ} {Γ = Γ} = isSetΣ (isSet→ (snd (fst Γ))) λ x → isSetΠ λ Δ* → isOfHLevelPath' 1 (isProp→isSet (SubSet (snd Γ (x Δ*)) (γˢ ∘ snd Δ Δ*))) 
D ._∘∙_ {γˢ = γ} {δˢ = δ} {Γ} {Δ} {Θ} γ∙ δ∙ = (λ Θ* →  fst γ∙ ((fst δ∙) Θ*)) , λ δ* → snd γ∙ (fst δ∙ δ*) ∙ cong (λ z → γ ∘ z) (snd δ∙ δ*) ∙ assoc γ δ (snd Θ δ*)
D .assoc∙ {γˢ = γˢ} {δˢ = δˢ} {θˢ = θˢ} {Γ} {Δ} {Θ} {Ξ} γ δ θ = λ i → (λ Ξ* → fst γ (fst δ (fst θ Ξ*))) , λ δ* → SubSet (snd Γ (fst γ (fst δ (fst θ δ*)))) (assoc γˢ δˢ θˢ i ∘ snd Ξ δ*) {! snd γ ?  !} {!   !} i 
D .id∙ {Γ} {Γ∙} = (λ Γ* → Γ*) , (λ δ*  → sym (idl (snd Γ∙ δ*)))
D .idr∙ γ = {!   !} --? , λ δ* → {! (snd γ δ*)  !}
D .idl∙ = {!!}
D .Ty∙ A = Σ (hSet lzero) λ A* → fst A* → Tm ◆ A
D .Tm∙ {Γ} {A} ((Γ* , _) , πΓ) ((A* , _) , πA) a = Σ (Γ* → A*) λ a* → (γ* : Γ*) → πA (a* γ*) ≡ a [ πΓ γ* ]
D .TmSet∙ {aˢ = aˢ}{Γ = Γ}{A = A} = isSetΣ (isSet→ (snd (fst A))) λ x → isSetΠ λ γ* → isOfHLevelPath' 1 (isProp→isSet (TmSet (snd A (x γ*)) (aˢ [ snd Γ γ* ])))
D ._[_]∙ {aˢ = aˢ}{γˢ = γˢ}{Δ = Δ}{A = A} γ δ = (λ Δ* → fst γ (fst δ Δ*)) , λ γ* → (snd γ (fst δ γ*) ∙ cong (λ z → aˢ [ z ]) (snd δ γ*)) ∙ []-∘ aˢ γˢ (snd Δ γ*) ∙ cong (λ z → (z [ snd Δ γ* ])) (sym ( aˢ [  γˢ ]=))
D .[]-∘∙ a γ δ = {!   !}
D .[]-id∙ = {!   !}
D ._▸∙_ Γ∙ A∙ = ((fst (fst A∙) × fst (fst Γ∙)) , isSet× (snd (fst A∙)) (snd (fst Γ∙))) , λ (a , Γ) → snd Γ∙ Γ , snd A∙ a 
D .p∙ = (λ x → snd x) , (λ δ* → sym (▸-β₁ _ _))
D .q∙ = (λ x → fst x) , (λ γ* → sym (▸-β₂ _ _))
D ._,∙_ = {!   !}
D .,-∘∙ = {!   !}
D .▸-β₁∙ = {!   !}
D .▸-β₂∙ = {!   !}
D .▸-η∙ = {!   !}
D .◆∙ = (Unit , (λ tt tt e e' → refl)) , λ tt → ε 
D .ε∙ = (λ Γ → tt) , (λ δ*  → sym (ε-∘ _))
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
 