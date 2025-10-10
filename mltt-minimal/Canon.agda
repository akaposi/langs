{-# OPTIONS --cubical #-}

-- --show-implicit
open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Transport
open import Cubical.Reflection.RecordEquiv

open import mltt-minimal.Syntax

open import mltt-minimal.Lib
module mltt-minimal.Canon where

-- open DepModel

module Canonicity where
  private variable
    Γ Δ Θ Ξ : Con
    γ γ₁ γ₂ δ θ σ : Sub Δ Γ
    A B : Ty Γ
    a a₁ a₂ b Â t : Tm Γ A
    u : Tm Γ U

  record Con∙ (Γ : Con) : Type₁ where
    no-eta-equality
    field
      ∣_∣ : hSet lzero
      π :  fst ∣_∣  → Sub ◇ Γ
  open Con∙ public
  
  private variable Γ∙ Δ∙ Θ∙ Ξ∙ : Con∙ Γ

  record Sub∙ (Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ)  : Type where
    no-eta-equality
    field
      ∣_∣ : fst  ∣ Δ∙ ∣ → fst ∣ Γ∙ ∣
      π :  ∀ (Δ* : fst Con∙.∣ Δ∙ ∣) → Con∙.π Γ∙ ∣ Δ* ∣ ≡ γ ∘ Con∙.π Δ∙ Δ*
  open Sub∙ public

  private unquoteDecl Sub-eqv = declareRecordIsoΣ Sub-eqv (quote Sub∙)

  SubSet∙ :  isSet (Sub∙ Δ∙ Γ∙ γ) 
  SubSet∙ {Δ∙ = Δ∙} {Γ∙ = Γ∙} {γ = γ} = isOfHLevelRetractFromIso 2 Sub-eqv (isSetΣ (isSet→ (snd ∣ Γ∙ ∣)) λ f → isSetΠ (λ Δ* → isProp→isSet (SubSet (π Γ∙ (f Δ*)) (γ ∘ π Δ∙ Δ*)))) 
 
  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : Sub∙ Δ∙ Γ∙ γ₁ → γ₁ ≡ γ₂ → Sub∙ Δ∙ Γ∙ γ₂ → Type
  _≡ˢ[_]_ {Δ∙ = Δ∙} {Γ∙ = Γ∙} γ₁ γ₁ˢ≡γ₂ˢ γ₂ = PathP (λ i → Sub∙ Δ∙ Γ∙ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂
 -- {A = λ i → ∀ δ → Γ .map (sem-path δ i) ≡ γ₁ˢ≡γ₂ˢ i S.∘ Δ .map δ}
  Sub-path : {γ₁∙ : Sub∙ Δ∙ Γ∙ γ₁} {γ₂∙ : Sub∙ Δ∙ Γ∙ γ₂}{γ₁ˢ≡γ₂ˢ : γ₁ ≡ γ₂} → (∀ δ → Sub∙.∣ γ₁∙ ∣ δ ≡ Sub∙.∣ γ₂∙ ∣ δ ) → γ₁∙ ≡ˢ[ γ₁ˢ≡γ₂ˢ ] γ₂∙ 
  ∣ Sub-path path i ∣ δ = path δ i
  Sub-path {Δ∙ = Δ∙} {Γ∙ = Γ∙} {γ₁ = γ₁} {γ₂ = γ₂} {γ₁ˢ≡γ₂ˢ = γ₁ˢ≡γ₂ˢ}  path i .π Δ* = {!    !}

  infixl 40 _∘∙_ 
  _∘∙_ :  {γ : Sub Δ Γ} {δ : Sub Θ Δ} → (γ∙ : Sub∙ Δ∙ Γ∙ γ) → (δ∙ : Sub∙ Θ∙ Δ∙ δ) → Sub∙ Θ∙ Γ∙ (γ ∘ δ)
  ∣ γ∙ ∘∙ δ∙ ∣ Θ* = ∣  γ∙ ∣  (∣ δ∙ ∣  Θ*)
  _∘∙_ {Δ∙ = Δ∙} {Γ∙ = Γ∙} {Θ∙ = Θ∙} {γ = γ} {δ = δ} γ∙ δ∙ .π  Θ* =  
    π Γ∙ (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*))     ≡⟨ π γ∙ (∣ δ∙ ∣ Θ*) ⟩
    γ ∘ Δ∙ .π (∣ δ∙ ∣ Θ*)                ≡⟨ cong (λ z → γ ∘ z) (π δ∙ Θ*) ⟩  
    γ ∘ (δ ∘ Θ∙ .π Θ*)                    ≡⟨ sym ass ⟩
    γ ∘ δ ∘ π Θ∙ Θ*      ∎
 
  ass∙ :  {γ∙ : Sub∙ Δ∙ Γ∙ γ} {δ∙ : Sub∙ Θ∙ Δ∙ δ}{θ∙ : Sub∙ Ξ∙ Θ∙ θ} 
          → γ∙ ∘∙ δ∙ ∘∙ θ∙  ≡ˢ[ ass ] γ∙ ∘∙ (δ∙ ∘∙ θ∙)
  ass∙ {γ∙ = γ∙} {δ∙ = δ∙} {θ∙ = θ∙} = Sub-path λ ξ → refl 

  id∙ : {Γ∙ : Con∙ Γ}  →  Sub∙ Γ∙ Γ∙ id 
  ∣ id∙ ∣  Γ* = Γ*
  id∙ .π Γ* = sym idl

  idr∙ : {γ∙ : Sub∙ Δ∙ Γ∙ γ} →  γ∙ ∘∙ id∙ ≡ˢ[ idr ] γ∙ 
  idr∙ {γ∙} = Sub-path λ δ → refl 

  idl∙ : {γ∙ : Sub∙ Δ∙ Γ∙ γ} → id∙ ∘∙ γ∙ ≡ˢ[ idl ] γ∙ 
  idl∙ {γ∙} = Sub-path λ δ → refl 

  record Ty∙ (Γ∙ : Con∙ Γ)(A : Ty Γ) : Type₁ where 
    no-eta-equality
    field
      ∣_∣ : UU
      π* :  ElU ∣_∣  → fst Con∙.∣ Γ∙ ∣ 
      π : (a* : ElU ∣_∣ ) → Tm ◇ (A [ Con∙.π Γ∙ (π* a*) ]T)
  open Ty∙ public
  private variable A∙ B∙ : Ty∙ Γ∙ A

  record Tm∙ (Γ∙ : Con∙ Γ) (A∙ : Ty∙ Γ∙ A) (a : Tm Γ A) : Type where
    no-eta-equality
    field
      ∣_∣ :  fst ∣ Γ∙ ∣ → ElU (Ty∙.∣_∣  A∙) 
      π* : {γ* : fst Con∙.∣ Γ∙ ∣ } → π* A∙ (∣ γ* ∣) ≡ γ*
      π : {γ* : fst Con∙.∣ Γ∙ ∣ } → π A∙ ∣ γ* ∣ ≡  a [ π Γ∙ (Ty∙.π* A∙ ∣ γ* ∣) ]t
  open Tm∙ public
-- λ {Γ A a Γ∙ A∙} → isSetΣ (isSetΠ λ Γ' →  isSetElU (A∙ .fst Γ')) λ f → isSetImplicitΠ (λ Γ' → isProp→isSet (TmSet (A∙ .snd (f Γ')) (a [ Γ∙ .snd Γ' ]t)))

  TmSet∙ : isSet (Tm∙ Γ∙ A∙ a)
  TmSet∙ = {!    !}

  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ∙ A∙} → Tm∙ Γ∙ A∙ a₁ → a₁ ≡ a₂ → Tm∙ Γ∙ A∙ a₂ → Type
  _≡ᵗ[_]_ {Γ∙ = Γ∙} {A∙ = A∙} a₁ a₁≡a₂ a₂ = PathP (λ i → Tm∙ Γ∙ A∙ (a₁≡a₂ i)) a₁ a₂

  Tm-path : {γ₁∙ : Sub∙ Δ∙ Γ∙ γ₁} {γ₂∙ : Sub∙ Δ∙ Γ∙ γ₂}{γ₁ˢ≡γ₂ˢ : γ₁ ≡ γ₂} → (∀ δ → Sub∙.∣ γ₁∙ ∣ δ ≡ Sub∙.∣ γ₂∙ ∣ δ ) → γ₁∙ ≡ˢ[ γ₁ˢ≡γ₂ˢ ] γ₂∙ 
  Tm-path x = {!  !}
  
  ◇∙ :  Con∙ ◇ -- Unit 
  ∣ ◇∙ ∣ = Unit , ((λ tt tt e e' → refl))
  ◇∙ .π = λ tt → ε

  ε∙ : Sub∙ Γ∙ ◇∙ ε
  ∣ ε∙ ∣ = λ x → tt
  ε∙ .π = λ δ* → (sym ◇η)

  infixl 4 _▹∙_ 
  _▹∙_ :  (Γ∙ : Con∙ Γ) → Ty∙ Γ∙ A → Con∙ (Γ ▹ A)
  ∣ Γ∙ ▹∙ A∙ ∣ = ((fst ∣ Γ∙ ∣) ×  ElU  ∣ A∙  ∣ ) , isSet× (snd ∣ Γ∙ ∣) (isSetElU ∣ A∙  ∣)
  (Γ∙ ▹∙ A∙) .π (a* , Γ*) = (Γ∙  .π  (A∙ .π*  Γ*)) ⁺ ∘ ⟨ A∙ .π   Γ* ⟩  

  ◇η∙ :  {σ∙ : Sub∙ Γ∙ ◇∙ σ} → σ∙ ≡ˢ[ ◇η ] ε∙
  ◇η∙ {σ∙ } = Sub-path λ δ → refl

  p∙ : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
  ∣ p∙ {Γ∙ = Γ∙} {A∙ = A∙} ∣ (Γ* , A*)  = Γ*
  p∙ {Γ∙ = Γ∙} {A∙ = A∙} .π  δ*@(Γ* , A*) = 
    π Γ∙ (δ* .fst) ≡⟨ congS (λ z → π Γ∙ z) {!refl  !} ⟩
    Γ∙ .π (A∙ .π* (δ* .snd))  ≡⟨ sym idr ⟩
    π Γ∙ (A∙ .π* (δ* .snd)) ∘ id  ≡⟨ cong (λ z → π Γ∙ (A∙ .π* (δ* .snd)) ∘ z)  (sym p∘⟨⟩) ⟩
    π Γ∙ (A∙ .π* (δ* .snd)) ∘ ( p ∘ ⟨ A∙ .π (δ* .snd) ⟩ )  ≡⟨ sym ass ⟩
    π Γ∙ (A∙ .π* (δ* .snd)) ∘ p ∘ ⟨ A∙ .π (δ* .snd) ⟩  ≡⟨ sym (cong ( λ z → z ∘ ⟨ A∙ .π (δ* .snd) ⟩) p∘⁺ ) ⟩
    p ∘ Γ∙ .π (A∙ .π* (δ* .snd)) ⁺ ∘ ⟨ A∙ .π (δ* .snd) ⟩  ≡⟨ ass ⟩
    p ∘ (Γ∙ .π (A∙ .π* (δ* .snd)) ⁺ ∘ ⟨ A∙ .π (δ* .snd) ⟩) ∎
  
  ⟨_⟩∙ : {t : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ Γ∙ A∙ t → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ t ⟩ 
  ∣ ⟨_⟩∙ a∙ ∣ Γ* = Γ* , (∣ a∙ ∣  Γ*)
  ⟨_⟩∙ {t = t} {Γ∙ = Γ∙} {A∙ = A∙} a∙ .π δ* =  
    Γ∙ .π (A∙ .π* (∣ a∙ ∣ δ*)) ⁺ ∘ ⟨ A∙ .π (∣ a∙ ∣ δ*) ⟩ ≡⟨ cong (λ z → Γ∙  .π (A∙ .π* (∣ a∙ ∣ δ*)) ⁺ ∘ ⟨ z ⟩ ) ( a∙ .π ) ⟩
    Γ∙ .π (A∙ .π* (∣ a∙ ∣ δ*)) ⁺ ∘ ⟨ t [ π Γ∙ (π* A∙ (∣ a∙ ∣ δ*)) ]t ⟩  ≡⟨ sym ⟨⟩∘ ⟩
    ⟨ t ⟩ ∘ Γ∙ .π (A∙ .π* (∣ a∙ ∣ δ*)) ≡⟨ cong (λ z → ⟨ t ⟩ ∘ Γ∙ .π z ) (a∙ .π* {δ*}) ⟩
    ⟨ t ⟩ ∘ π Γ∙ δ* ∎

  p∘⟨⟩∙ : {a∙ : Tm∙ Γ∙ A∙ a} → p∙ ∘∙ ⟨ a∙ ⟩∙ ≡ˢ[ p∘⟨⟩ ] id∙
  p∘⟨⟩∙ = Sub-path λ δ → refl

    -- ; _[_]T∙ = λ {Δ Γ A γ Δ∙ Γ∙} A∙ γ∙ → (λ δ* → fst A∙ (fst γ∙ δ*)) , (λ {γ*} e → subst (Tm ◇) [∘]T ((subst (λ z → Tm ◇ (A [ z ]T)) (snd γ∙ γ*) ((snd A∙ e )))))
 -- Δ∙ .snd γ* 
 
  _[_]T∙ : {A : Ty Γ}{γ : Sub Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ} → Ty∙ Γ∙ A → Sub∙ Δ∙ Γ∙ γ → Ty∙ Δ∙ (A [ γ ]T)
  ∣ _[_]T∙ {A = A} {γ = γ} {Δ∙ = Δ∙} {Γ∙ = Γ∙} A∙ γ∙ ∣ = ∣ A∙ ∣
  _[_]T∙ {A = A} {γ = γ} {Δ∙ = Δ∙} {Γ∙ = Γ∙} A∙ γ∙ .π* A* = {!   !} --(A∙ [ γ∙ ]T∙) .π*  A*
  _[_]T∙ {A = A} {γ = γ} {Δ∙ = Δ∙} {Γ∙ = Γ∙} A∙ γ∙ .π a* = {!   !}

open import mltt-minimal.DepModel as D

Canons : D.DepModel 
Canons = record
  { Con∙ = Canonicity.Con∙
  ; Sub∙ = Canonicity.Sub∙
  ; Ty∙ = Canonicity.Ty∙
  ; Tm∙ = Canonicity.Tm∙
  ; _▹∙_ = Canonicity._▹∙_
  ; ◇∙ = Canonicity.◇∙
  ; SubSet∙ = Canonicity.SubSet∙
  ; TySet∙ = {!   !}
  ; TmSet∙ = Canonicity.TmSet∙
  ; _∘∙_ = Canonicity._∘∙_
  ; ass∙ = Canonicity.ass∙
  ; id∙ = Canonicity.id∙
  ; idl∙ = Canonicity.idl∙ 
  ; idr∙ = Canonicity.idr∙
  ; ε∙ = Canonicity.ε∙
  ; ◇η∙ = Canonicity.◇η∙
  ; p∙ = Canonicity.p∙
  ; ⟨_⟩∙ = Canonicity.⟨_⟩∙
  ; p∘⟨⟩∙ = Canonicity.p∘⟨⟩∙
  ; _[_]T∙ = {!   !}
  ; [∘]T∙ = {!   !}
  ; [id]T∙ = {!   !}
  ; [p][⟨⟩]T∙ = {!   !}
  ; U∙ = {!   !}
  ; U[]∙ = {!   !}
  ; El∙ = {!   !}
  ; Π∙ = {!   !}
  ; _[_]t∙ = {!   !}
  ; q∙ = {!   !}
  ; q[⟨⟩]∙ = {!   !}
  ; [∘]t∙ = {!   !}
  ; [id]t∙ = {!   !}
  ; _[_]U∙ = {!   !}
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