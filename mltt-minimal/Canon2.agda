{-# OPTIONS --cubical #-}

-- --show-implicit
open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import mltt-minimal.Syntax as I
open import mltt-minimal.DepModel
-- open import mltt-minimal.InitialModel
open import mltt-minimal.Lib
module mltt-minimal.Canon2 where

open DepModel



Canon2 : DepModel 
Canon2 = record
  {  Con∙ = λ Γ → Σ (hSet lzero) λ Γ* → fst Γ* → Sub ◇ Γ
  ; Sub∙ = λ ((Δ* , _ ) , πΔ) ((Γ* , _ ) , πΓ)  γ → Σ (Δ* → Γ*) λ γ* → (δ* : Δ*) → πΓ (γ* δ*) ≡ γ ∘ πΔ δ*
  ; Ty∙ = λ ((Γ* , _) , πΓ) A → Σ (Γ* → UU) λ A* → {γ* : Γ*} → ElU (A* γ*) → Tm ◇ (A [ πΓ γ* ]T) 
  ; Tm∙ = λ ((Γ* , _) , πΓ)  (A* , πA) a → Σ ((γ* : Γ*) → ElU (A* γ*)) λ a* → {γ* : Γ*} → πA (a* γ*) ≡ a [ πΓ γ* ]t
  ; _▹∙_ = λ {Γ A} Γ∙ A∙ → (Σ (fst (fst Γ∙)) (λ γ* → ElU (fst A∙ γ*))  , 
    isSetΣ (snd (fst Γ∙)) λ Γ' → isSetElU (fst A∙ Γ')) , λ (a* , Γ*) →  (snd Γ∙ a*) ⁺ ∘  ⟨ snd A∙ Γ* ⟩ -- snd A∙ Γ* 
  ; ◇∙ = (Unit , (λ tt tt e e' → refl)) , λ tt → ε
  ; SubSet∙ = λ {Δ Γ γ Δ∙ Γ∙} → isSetΣ (isSet→ (snd (fst Γ∙))) λ x → isSetΠ λ Δ* → isOfHLevelPath' 1 (isProp→isSet (SubSet (snd Γ∙ (x Δ*)) (γ ∘ snd Δ∙ Δ*)))
  ; TySet∙ = λ {Γ A Γ∙} → isSetΣ (isSet→ isSetUU) λ x → isSetImplicitΠ (λ Γ' → isSetΠ λ ΓU → TmSet)
  ; TmSet∙ =  λ {Γ A a Γ∙ A∙} → isSetΣ (isSetΠ λ Γ' →  isSetElU (A∙ .fst Γ')) λ f → isSetImplicitΠ (λ Γ' → isProp→isSet (TmSet (A∙ .snd (f Γ')) (a [ Γ∙ .snd Γ' ]t)))
  ; _∘∙_ = λ  {Δ}{Γ}{Θ}{γ}{δ} γ∙ δ∙ → (λ Θ* → fst γ∙ ((fst δ∙) Θ*)) , λ δ* → snd γ∙ (fst δ∙ δ*) ∙ cong (λ z → γ ∘ z) (snd δ∙ δ*) ∙ sym ass -- 
  ; ass∙ = ΣPathP (refl , (funExt (λ Ξ* → toPathP (SubSet _ _ _ _))))
  ; id∙ = (λ Γ* → Γ*) , λ δ* → sym idl
  ; idl∙ = ΣPathP (refl , funExt (λ Δ' → toPathP (SubSet _ _ _ _)))
  ; idr∙ = ΣPathP (refl , funExt (λ Δ' → toPathP (SubSet _ _ _ _)))
  ; ε∙ = (λ x → tt) , (λ δ* → (sym ◇η))
  ; ◇η∙ = ΣPathP (refl , funExt (λ Δ' → toPathP (SubSet _ _ _ _))) 
  ; p∙ = λ {Γ A Γ∙ A∙} → (λ Γ' → fst Γ') , λ δ* → sym (sym ass ∙ cong ( λ z → z ∘  ⟨ snd A∙ (δ* .snd) ⟩) p∘⁺  ∙ ass  ∙ cong (λ z → Γ∙ .snd (δ* .fst) ∘ z)  p∘⟨⟩ ∙ idr) 
  ; ⟨_⟩∙ = λ {Γ A t Γ∙ A∙} Γ* → (λ Γ' → Γ' , fst Γ* Γ') , λ δ* → cong (λ z → snd Γ∙ δ* ⁺ ∘ ⟨ z ⟩ ) (snd Γ* {δ*}) ∙ sym ⟨⟩∘
  ; p∘⟨⟩∙ = ΣPathP (refl , (funExt (λ Γ'  → toPathP (SubSet _ _ _ _))))                                                                                            --  A [ γ ∘ Δ∙ .snd (fst δ∙ Θ') ]T  ≡ A [ γ ∘ δ ∘ Θ∙ .snd Θ' ]T
  ; _[_]T∙ = λ {Δ Γ A γ Δ∙ Γ∙} A∙ γ∙ → (λ δ* → fst A∙ (fst γ∙ δ*)) , (λ {γ*} e → subst (Tm ◇) [∘]T ((subst (λ z → Tm ◇ (A [ z ]T)) (snd γ∙ γ*) ((snd A∙ e )))))-- ∙ cong (λ z → A [ γ ∘ z ]T) ? --  A [ γ ∘ δ ∘ Θ∙ .snd Θ' ]T --  A [ γ ∘ Δ∙ .snd (fst δ∙ Θ') ]T -- cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ'))
  --; [∘]T∙ = λ {Δ Γ Θ A γ δ Δ∙ Γ∙ Θ∙ A∙ γ∙ δ∙} → ΣPathP (refl , (implicitFunExt λ {Θ'} → funExt (λ eA → toPathP ( cong (transport (λ z → Tm ◇ ([∘]T z [ Θ∙ .snd Θ' ]T))) (sym (substComposite (Tm ◇)  (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ'))  ∙  (cong (λ z → A [ γ ∘ z ]T) (snd δ∙ Θ') ∙ cong (λ z → A [ z ]T) ((sym (ass {γ = γ} {δ = δ} {θ =  Θ∙ .snd Θ'}))) )) [∘]T (snd A∙ eA))) ∙   (sym (substComposite (Tm ◇)  (((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ (λ i → A [ γ ∘ snd δ∙ Θ' i ]T) ∙ (λ i → A [ ass (~ i) ]T)) ∙ [∘]T) {!   !} (snd A∙ eA)) ∙ ( ( cong (λ z → subst (Tm ◇) z  (snd A∙ eA)) ? ∙ substComposite (Tm ◇) ((((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) ∙ (λ i → A {!   !} γ ]T [ snd δ∙ Θ' i ]T))) [∘]T (snd A∙ eA)) ∙ cong (subst (Tm ◇) [∘]T) (substComposite (Tm ◇) ((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) (cong (λ z → A [ γ ]T [ z ]T) (snd δ∙ Θ'))  (snd A∙ eA)) ∙ cong (λ z → subst (Tm ◇) [∘]T  (subst (λ z → Tm ◇ (A [ γ ]T [ z ]T)) (snd δ∙ Θ') z)) (substComposite (Tm ◇) (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ')))  [∘]T (snd A∙ eA)) ) ) ) )))
  -- ; [∘]T∙ = λ {Δ Γ Θ A γ δ Δ∙ Γ∙ Θ∙ A∙ γ∙ δ∙} → ΣPathP (refl , (implicitFunExt λ {Θ'} → funExt (λ eA → toPathP ( cong (transport (λ z → Tm ◇ ([∘]T z [ Θ∙ .snd Θ' ]T))) (sym (substComposite (Tm ◇)  (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ'))  ∙  (cong (λ z → A [ γ ∘ z ]T) (snd δ∙ Θ') ∙ cong (λ z → A [ z ]T) ((sym (ass {γ = γ} {δ = δ} {θ =  Θ∙ .snd Θ'}))) )) [∘]T (snd A∙ eA))) ∙   (sym (substComposite (Tm ◇)  (((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ (λ i → A [ γ ∘ snd δ∙ Θ' i ]T) ∙ (λ i → A [ ass (~ i) ]T)) ∙ [∘]T)  (cong  (λ z → z [ Θ∙ .snd Θ' ]T) ([∘]T {γ = γ} {δ = δ})) (snd A∙ eA)) 
  -- ∙ ( (  (cong (λ z → subst (Tm ◇) z (snd A∙ eA)) (TySet _ _ _ _)) ∙ substComposite (Tm ◇) (((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) ∙  (λ i → A [ γ ]T [ snd δ∙ Θ' i ]T))  [∘]T (snd A∙ eA)) ∙ cong (subst (Tm ◇) [∘]T) (substComposite (Tm ◇) ((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) (cong (λ z → A [ γ ]T [ z ]T) (snd δ∙ Θ'))  (snd A∙ eA)) ∙ cong (λ z → subst (Tm ◇) [∘]T  (subst (λ z → Tm ◇ (A [ γ ]T [ z ]T)) (snd δ∙ Θ') z)) (substComposite (Tm ◇) (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ')))  [∘]T (snd A∙ eA)) ) ) ) )))
  ; [∘]T∙ = λ {Δ Γ Θ A γ δ Δ∙ Γ∙ Θ∙ A∙ γ∙ δ∙} → 
      ΣPathP (refl , 
        (implicitFunExt λ {Θ'} → funExt (λ eA → toPathP (  (cong (transport (λ z → Tm ◇ ([∘]T z [ Θ∙ .snd Θ' ]T)))  (sym (substComposite (Tm ◇) (cong (λ z → A [ z ]T ) (snd γ∙ (fst δ∙ Θ')) ∙ cong (λ z →  A [ γ ∘ z ]T) (snd δ∙ Θ') ∙ cong (λ z → A [ z ]T) ((sym (ass {γ = γ} {δ = δ} {θ =  Θ∙ .snd Θ'})))) [∘]T (snd A∙ eA))) ∙ {! ?  ∙  sym (substComposite (Tm ◇) (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ')))  [∘]T (snd A∙ eA))!} ) ∙ ( (  (cong (λ z → subst (Tm ◇) z (snd A∙ eA)) (TySet _ _ _ _)) ∙ substComposite (Tm ◇) (((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) ∙  (λ i → A [ γ ]T [ snd δ∙ Θ' i ]T))  [∘]T (snd A∙ eA)) ∙ cong (subst (Tm ◇) [∘]T) (substComposite (Tm ◇) ((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) (cong (λ z → A [ γ ]T [ z ]T) (snd δ∙ Θ'))  (snd A∙ eA)) ∙ cong (λ z → subst (Tm ◇) [∘]T  (subst (λ z → Tm ◇ (A [ γ ]T [ z ]T)) (snd δ∙ Θ') z)) (substComposite (Tm ◇) (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ')))  [∘]T (snd A∙ eA)) ) ) ) ))
-- two yellow -- congS (subst (λ e → Tm ◇ (e [ Θ∙ .snd Θ' ]T)) [∘]T)  -- subst (λ e → Tm ◇ (e [ Θ∙ .snd Θ' ]T)) [∘]T _x_852
  -- with subst
  -- ; [∘]T∙ = λ {Δ Γ Θ A γ δ Δ∙ Γ∙ Θ∙ A∙ γ∙ δ∙} → ΣPathP (refl , implicitFunExt (λ {Θ'} → funExt λ eA → toPathP ({! congS (subst (λ e → Tm ◇ (e [ Θ∙ .snd Θ' ]T)) ([∘]T )) ? !} ∙  ( (  (cong (λ z → subst (Tm ◇) z (snd A∙ eA)) (TySet _ _ _ _)) ∙ substComposite (Tm ◇) (((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) ∙  (λ i → A [ γ ]T [ snd δ∙ Θ' i ]T))  [∘]T (snd A∙ eA)) ∙ cong (subst (Tm ◇) [∘]T) (substComposite (Tm ◇) ((λ i → A [ snd γ∙ (fst δ∙ Θ') i ]T) ∙ [∘]T) (cong (λ z → A [ γ ]T [ z ]T) (snd δ∙ Θ'))  (snd A∙ eA)) ∙ cong (λ z → subst (Tm ◇) [∘]T  (subst (λ z → Tm ◇ (A [ γ ]T [ z ]T)) (snd δ∙ Θ') z)) (substComposite (Tm ◇) (cong (λ z → A [ z ]T) (snd γ∙ (fst δ∙ Θ')))  [∘]T (snd A∙ eA)) )  ) ) ) 
  
  ; [id]T∙ = λ  {Γ A Γ∙ A∙} →  ΣPathP (refl , (implicitFunExt (λ {Γ} → funExt λ e → toPathP (cong (transport (λ z → Tm ◇ ([id]T z [ Γ∙ .snd Γ ]T))) (sym (substComposite (Tm ◇) ((cong (λ z → A [ z ]T) (sym (idl {γ = Γ∙ .snd Γ})))) [∘]T (snd A∙ e))) ∙ sym  (substComposite (Tm ◇)  ((λ i → A [ idl {γ = (Γ∙ .snd Γ)} (~ i) ]T) ∙ [∘]T) (cong (λ z → z [ Γ∙ .snd Γ ]T) [id]T) (snd A∙ e)) ∙ cong (λ z → subst (Tm ◇) z (snd A∙ e)) (TySet _ _ (λ i → refl i) λ i → A [ Γ∙ .snd Γ ]T) ∙  substRefl  {B = (Tm ◇)} {x = (A [ Γ∙ .snd Γ ]T)} (A∙ .snd e))))) 
  ; [p][⟨⟩]T∙ = λ {Γ A B b Γ∙ A∙ B∙ b∙} → ΣPathP (refl , (implicitFunExt (λ {Γ'} → funExt (λ eA → toPathP {!  subst !}))))
  ; U∙ = (λ x → ⊥U) , (λ x → exfalso x)
  ; U[]∙ = λ {Δ Γ γ Δ∙ Γ∙ γ∙} → ΣPathP (refl , (implicitFunExt λ {Δ'} → funExt λ x → exfalso x))
  ; El∙ = λ {Γ Â Γ∙} γ∙ → (λ Γ' → ⊥U) , λ x → exfalso x
  ; Π∙ = λ {Γ A B Γ∙} A∙ B∙ → fst A∙ , λ {γ*} eA  →  subst (Tm ◇) (sym Π[] ) ((lam {!  !}) [ (snd Γ∙  γ*) ]Π) -- subst (Tm ◇) (sym Π[]) (lam {!   !} [ snd Γ∙ γ* ]Π)
  --   [p][⁺]T    : A [ p {A = B} ]T [ γ ⁺ ]T ≡ A [ γ ]T [ p ]T  -- ⟨ (snd A∙ eA) ⟩ 
  -- [p⁺][⟨q⟩]T : A [ p ⁺ ]T [ ⟨ q ⟩ ]T ≡ A
  -- [⟨⟩][]T    : A [ ⟨ a ⟩ ]T [ γ ]T ≡ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
  -- El[]       : El Â [ γ ]T ≡ El (Â [ γ ]U)
  -- Π[]        : Π A B [ γ ]T ≡ Π (A [ γ ]T) (B [ γ ⁺ ]T)
  ; _[_]t∙ = λ {Δ Γ A a γ Δ∙ Γ∙ A∙} → λ a∙ γ∙ → (λ γ* → fst a∙ (fst γ∙ γ*)) , λ {γ*} → sym (substComposite (Tm ◇) (cong (λ z → A [ z ]T ) (snd γ∙ γ*)) [∘]T   (snd A∙ (fst a∙ (fst γ∙ γ*)))) ∙ cong (subst (Tm ◇) ((λ i → A [ snd γ∙ γ* i ]T) ∙ [∘]T)) (snd a∙ {(fst γ∙ γ*)}) ∙ sym (subst2r (Tm ◇) (cong (λ z → A [ z ]T ) (snd γ∙ γ*) ∙ [∘]T {A = A}  {γ = γ} {δ = Δ∙ .snd γ*}) {!   !}) ∙ fromPathP ([∘]t {γ = γ} {δ = (Δ∙ .snd γ*)}) --cong (subst (Tm ◇) ((λ i → A {!   !} snd γ∙ γ* i ]T) ∙ [∘]T)) {! cong (λ z → A [ z ]T) (snd γ∙ γ* ) !} ∙ {!   !}
  ; q∙ =   λ {Γ A Γ∙ A∙} → (λ γ* → snd γ*) , λ {γ*} → sym  (substComposite  (Tm ◇) (cong (λ z → A [ z ]T) (sym (sym ass ∙ cong (λ z → z ∘ ⟨ snd A∙ (γ* .snd) ⟩) p∘⁺ ∙ ass ∙ cong (λ z → Γ∙ .snd (γ* .fst) ∘ z)   p∘⟨⟩ ∙ idr))) [∘]T (snd A∙ (snd γ*))) ∙  cong (λ z → subst (Tm ◇) z (snd A∙ (snd γ*))) (TySet _ _ _ _) ∙ sym (fromPathP⁻ ([∘]t {γ = (snd Γ∙ (γ* .fst) ⁺)} {δ =  ⟨ snd A∙ (γ* .snd) ⟩} {a = q}) ∙ {!   !} ) --{!   !} ∙ fromPathP (cong (λ z → transport⁻ ((λ i → Tm ◇ ([∘]T i))) (z [ ⟨ snd A∙ (γ* .snd) ⟩ ]t) )  (fromPathP q[⁺]))) ∙ refl  --fromPathP (cong {!   !} (fromPathP q[⁺])) ∙ {!   !})
  ; q[⟨⟩]∙ = {!   !}
  ; [∘]t∙ = {!   !}
  ; [id]t∙ = {!   !}
  ; _[_]U∙ = λ {Δ Γ u γ Δ∙ Γ∙} u∙ γ∙ → (λ γ* → fst u∙ (fst γ∙ γ*)) , λ {γ*} →  {! (fromPathP ([∘]t {γ = γ} {δ = Δ∙ .snd γ*} {a = u}))  !} ∙ cong (λ z → z [ Δ∙ .snd γ* ]t) (fromPathP []U)  -- snd u∙ {(fst γ∙ γ*)} i
  ; []U∙ = {!   !}
  ; _⁺∙ = {!   !}
  ; ∘⁺∙ = {!   !}
  ; id⁺∙ = {!   !}
  ; p∘⁺∙ = {!   !}
  ; ⟨⟩∘∙ = {!   !}
  ; p⁺∘⟨q⟩∙ = {!   !}
  ; [p][⁺]T∙ = {!   !}
  ; [p⁺][⟨q⟩]T∙ = {!   !}
  ; [⟨⟩][]T∙ = {!   !}
  ; El[]∙ = {!   !}
  ; Π[]∙ = {!   !}
  ; q[⁺]∙ = {!   !}
  ; _[_]Π∙ = {!   !}
  ; []Π∙ = {!   !}
  ; lam∙ = {!   !}
  ; app∙ = {!   !}
  ; Πβ∙ = {!   !}
  ; Πη∙ = {!   !}
  ; lam[]∙ = {!   !}
  ; app[]∙ = {!   !}
  }

