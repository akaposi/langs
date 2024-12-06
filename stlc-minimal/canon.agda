{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import Cubical.Data.Empty renaming (rec to exfalso)
open import stlc-minimal.Syntax as I
import stlc-minimal.DepModel as Mod
open import stlc-minimal.InitialModel
open import Cubical.Foundations.Transport

open import stlc-minimal.Lib

open import stlc-minimal.DepModel

module stlc-minimal.canon where

open DepModel
  
D : DepModel InStrict 
D .Con∙ Γ = Σ (hSet lzero) λ Γ* → fst Γ* → Sub ◆ Γ
D .Sub∙ {Δ} {Γ} ((Δ* , _) , πΔ) ((Γ* , _) , πΓ) γ = Σ (Δ* → Γ*) λ γ* → (δ* : Δ*) → πΓ (γ* δ*) ≡ γ ∘ πΔ δ*
D .SubSet∙ {γˢ = γˢ} {Δ = Δ} {Γ = Γ} = isSetΣ (isSet→ (snd (fst Γ))) λ x → isSetΠ λ Δ* → isOfHLevelPath' 1 (isProp→isSet (SubSet (snd Γ (x Δ*)) (γˢ ∘ snd Δ Δ*))) 
D ._∘∙_ {γˢ = γ} {δˢ = δ} {Γ} {Δ} {Θ} γ∙ δ∙ = (λ Θ* →  fst γ∙ ((fst δ∙) Θ*)) , λ δ* → snd γ∙ (fst δ∙ δ*) ∙ cong (λ z → γ ∘ z) (snd δ∙ δ*) ∙ assoc γ δ (snd Θ δ*)
D .assoc∙ γ δ θ = ΣPathP (refl ,  funExt λ Ξ* →  toPathP (SubSet _ _ _ _)) 
D .id∙ {Γ} {Γ∙} = (λ Γ* → Γ*) , (λ δ*  → sym (idl (snd Γ∙ δ*)))
D .idr∙ γ = ΣPathP (refl , funExt (λ Δ' → toPathP (SubSet _ _ _ _)))  
D .idl∙ γ = ΣPathP (refl , funExt (λ Δ* → toPathP (SubSet _ _ _ _)))
D .Ty∙ A = Σ (hSet lzero) λ A* → fst A* → Tm ◆ A
D .Tm∙ {Γ} {A} ((Γ* , _) , πΓ) ((A* , _) , πA) a = Σ (Γ* → A*) λ a* → (γ* : Γ*) → πA (a* γ*) ≡ a [ πΓ γ* ]
D .TmSet∙ {aˢ = aˢ}{Γ = Γ}{A = A} = isSetΣ (isSet→ (snd (fst A))) λ x → isSetΠ λ γ* → isOfHLevelPath' 1 (isProp→isSet (TmSet (snd A (x γ*)) (aˢ [ snd Γ γ* ])))
D ._[_]∙ {aˢ = aˢ}{γˢ = γˢ}{Δ = Δ}{A = A} γ δ = (λ Δ* → fst γ (fst δ Δ*)) , λ γ* → (snd γ (fst δ γ*) ∙ cong (λ z → aˢ [ z ]) (snd δ γ*)) ∙ []-∘ aˢ γˢ (snd Δ γ*) ∙ cong (λ z → (z [ snd Δ γ* ])) (sym ( aˢ [  γˢ ]=))
D .[]-∘∙ a γ δ = ΣPathP (refl , funExt (λ Θ → toPathP (TmSet _ _ _ _)))
D .[]-id∙ a = ΣPathP (refl , funExt (λ Θ → toPathP (TmSet _ _ _ _)))
D ._▸∙_ Γ∙ A∙ = ((fst (fst A∙) × fst (fst Γ∙)) , isSet× (snd (fst A∙)) (snd (fst Γ∙))) , λ (a , Γ) → snd Γ∙ Γ , snd A∙ a 
D .p∙ = (λ x → snd x) , (λ δ* → sym (▸-β₁ _ _))
D .q∙ = (λ x → fst x) , (λ γ* → sym (▸-β₂ _ _))
D ._,∙_ {γˢ = γˢ} {aˢ = aˢ} {Γ} {Δ} {A} (Γ* , πΓ) (A* , πA) = (λ x → A* x , Γ* x), λ δ* → (cong (λ z → (z , snd A (A* δ*))) (πΓ _) ∙ (cong (λ z → (γˢ ∘ snd Δ δ* , z)) (πA _))) ∙ sym (,-∘ _ _ _)
D .,-∘∙ γ a δ = ΣPathP (refl , (funExt λ Θ → toPathP (SubSet _ _ _ _)))
D .▸-β₁∙ γ a = ΣPathP (refl , (funExt λ Θ → toPathP (SubSet _ _ _ _))) 
D .▸-β₂∙ γ a = ΣPathP (refl , (funExt λ Θ → toPathP (TmSet _ _ _ _)))
D .▸-η∙ = ΣPathP (refl , (funExt λ Θ → toPathP (SubSet _ _ _ _))) 
D .◆∙ = (Unit , (λ tt tt e e' → refl)) , λ tt → ε 
D .ε∙ = (λ Γ → tt) , (λ δ*  → sym (ε-∘ _))
D .ε-∘∙ γ = ΣPathP (refl , (funExt λ Θ → toPathP (SubSet _ _ _ _))) 
D .◆-η∙ = ΣPathP (refl , (funExt λ Θ → toPathP (SubSet _ _ _ _))) 
D ._⇒∙_ {Aˢ} {Bˢ} A* B* = (Σ (Tm ◆ (Aˢ ⇒ Bˢ)) (λ x → Σ (fst (fst A*) → fst (fst B*)) λ y → ∀ a → snd B* (y a) ≡ app x (snd A* a)) , isSetΣ TmSet λ x → isSetΣ (isSet→ (snd (fst B*))) λ f → isSetΠ λ a' → isProp→isSet (TmSet _ _)) , λ x → fst x   
D .app∙ {Γˢ} {Aˢ} {Bˢ} {fˢ = fˢ} {aˢ} {Γ = Γ} {A} {B} (f , fγ) (a , fa) = (λ Γ* → fst (snd (f Γ*)) (a Γ*)) , λ Γ* → snd (snd (f Γ*)) (a Γ*) ∙ cong (λ z → app (fst (f Γ*)) z) (fa Γ*) ∙ cong (λ z → app z (aˢ [ snd Γ Γ* ])) (fγ Γ*) ∙ sym (app-[] _ _ _) 
D .app-[]∙ f a γ = ΣPathP (refl , (funExt λ Θ → toPathP (TmSet _ _ _ _)))
D .lam∙ {bˢ = bˢ} {Γ} {A} {B} (B* , γ-[]) = (λ Γ* → (lam (bˢ [ ((snd Γ Γ*) I.↑) ])) , ((λ A* → B* (A* , Γ*)) , λ a → γ-[] (a , Γ*) ∙ (cong (λ z → bˢ [ z ]) (sym (I.↑-⟨⟩ _ _)) ∙ ([]-∘ bˢ _ _)) ∙ sym (⇒-β ((bˢ [ snd Γ Γ* I.↑ ])) (snd A a)))) , λ γ* → sym (lam-[] _ _) 
D .lam-[]∙ {bˢ = bˢ} {γˢ = γˢ} {Γ} {Δ} {A} {B} b γ = ΣPathP (funExt (λ Δ* → ΣPathP (cong (λ z → lam (bˢ [ z I.↑ ])) (snd γ Δ*) ∙ cong ( λ z → lam (bˢ [ z ])) (↑-∘ γˢ (snd Δ Δ*)) ∙ cong (λ z → lam z) ([]-∘ bˢ (γˢ ∘ p , q) (snd Δ Δ* I.↑)) ∙ cong (λ z → lam (z [ snd Δ Δ* ∘ p , q ])) (sym (bˢ [ γˢ ∘ p , q  ]=)) , ΣPathP (refl , funExt (λ A* → toPathP (TmSet _ _ _ _))))) , (funExt (λ Δ* → toPathP (TmSet _ _ _ _))))                 
D .⇒-β∙ b a = ΣPathP (refl , (funExt λ Θ → toPathP (TmSet _ _ _ _))) 
D .⇒-η∙ {fˢ = fˢ} {Γ} {A} {B} f = ΣPathP (funExt (λ Γ* → ΣPathP (((cong (λ z → lam (app z q [ snd Γ Γ* I.↑ ])) (fˢ [ p ]=)  ∙ cong (λ z → lam z) (app-[] (fˢ [ p ]) q (snd Γ Γ* I.↑)) ∙ cong (λ z → lam (app ((fˢ [ p ]) [ snd Γ Γ* I.↑ ]) z)) (▸-β₂ _ q) ∙ (cong (λ z → lam (app z q)) (sym ([]-∘ fˢ p (snd Γ Γ* I.↑))) ∙ cong (λ z → lam (app (fˢ [ z ]) q))  (▸-β₁ _ _)) ∙ cong (λ z → lam (app z q)) ([]-∘ fˢ (snd Γ Γ*) p)) ∙ ⇒-η (fˢ [ snd Γ Γ* ])) ∙ sym (snd f Γ*) , ΣPathP (refl , funExt (λ A* → toPathP (TmSet _ _ _ _))))) , funExt (λ Γ* → toPathP (TmSet _ _ _ _))) 
D .ι∙ =  (⊥ , λ {()}) , (λ x → exfalso x)                                                                                                                                                                                   
              