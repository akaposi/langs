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
open import Cubical.Foundations.Path

open import mltt-minimal.Syntax

open import mltt-minimal.Lib2
module mltt-minimal.Canon where

-- open DepModel

module Canonicity where
  private variable
    Γ Δ Θ Ξ : Con
    γ γ₁ γ₂ δ θ σ : Sub Δ Γ
    A B A₁ A₂ : Ty Γ
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
  -- private variable γ∙  δ∙ : Sub∙ Γ∙ ?
  private unquoteDecl Sub-eqv = declareRecordIsoΣ Sub-eqv (quote Sub∙)

  SubSet∙ :  isSet (Sub∙ Δ∙ Γ∙ γ) 
  SubSet∙ {Δ∙ = Δ∙} {Γ∙ = Γ∙} {γ = γ} = isOfHLevelRetractFromIso 2 Sub-eqv (isSetΣ (isSet→ (snd ∣ Γ∙ ∣)) λ f → isSetΠ (λ Δ* → isProp→isSet (SubSet (π Γ∙ (f Δ*)) (γ ∘ π Δ∙ Δ*)))) 
 
  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : Sub∙ Δ∙ Γ∙ γ₁ → γ₁ ≡ γ₂ → Sub∙ Δ∙ Γ∙ γ₂ → Type
  _≡ˢ[_]_ {Δ∙ = Δ∙} {Γ∙ = Γ∙} γ₁ γ₁ˢ≡γ₂ˢ γ₂ = PathP (λ i → Sub∙ Δ∙ Γ∙ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂

  Sub-path : {γ₁∙ : Sub∙ Δ∙ Γ∙ γ₁} {γ₂∙ : Sub∙ Δ∙ Γ∙ γ₂}{γ₁ˢ≡γ₂ˢ : γ₁ ≡ γ₂} → (∀ δ → Sub∙.∣ γ₁∙ ∣ δ ≡ Sub∙.∣ γ₂∙ ∣ δ ) → γ₁∙ ≡ˢ[ γ₁ˢ≡γ₂ˢ ] γ₂∙ 
  ∣ Sub-path path i ∣ δ = path δ i
  Sub-path {Δ∙ = Δ∙} {Γ∙ = Γ∙} {γ₁ = γ₁} {γ₂ = γ₂}{γ₁∙ = γ₁∙}{γ₂∙ = γ₂∙}{γ₁ˢ≡γ₂ˢ = γ₁ˢ≡γ₂ˢ}  path i .π Δ* = isProp→PathP {B = λ i → π Γ∙ (path Δ* i) ≡ γ₁ˢ≡γ₂ˢ i ∘ π Δ∙ Δ*} ((λ i₁ → SubSet _ _)) (γ₁∙ .π  Δ*)
    (γ₂∙ .π  Δ*) i

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
      ∣_∣ : fst ∣ Γ∙ ∣ → UU
      π :  (Γ* : fst Con∙.∣ Γ∙ ∣) → ElU ∣ Γ* ∣  → Tm ◇ (A [ Con∙.π  Γ∙  Γ* ]T) 
  open Ty∙ public
  private unquoteDecl Ty-eqv = declareRecordIsoΣ Ty-eqv (quote Ty∙)
  private variable A∙ B∙ A₁∙ A₂∙ : Ty∙ Γ∙ A

  record Tm∙ (Γ∙ : Con∙ Γ) (A∙ : Ty∙ Γ∙ A) (a : Tm Γ A) : Type where
    no-eta-equality
    field
      ∣_∣ :  (γ* : fst ∣ Γ∙ ∣) → ElU (∣ A∙ ∣ γ*)
      π : (Γ* : fst Con∙.∣ Γ∙ ∣) → Ty∙.π A∙  Γ*  ∣ Γ* ∣ ≡ a [ Γ∙ .π  Γ* ]t

  open Tm∙ public
  private unquoteDecl Tm-eqv = declareRecordIsoΣ Tm-eqv (quote Tm∙)

  TySet∙ : isSet (Ty∙ Γ∙ A)
  TySet∙ = isOfHLevelRetractFromIso 2 Ty-eqv (isSetΣ (isSet→ isSetUU) λ fu → isSetΠ (λ Γ* → isSet→ TmSet))  
  
  TmSet∙ : isSet (Tm∙ Γ∙ A∙ a)
  TmSet∙ {Γ∙ = Γ∙}{A∙ = A∙}{a = a}  = isOfHLevelRetractFromIso 2 Tm-eqv (isSetΣ (isSetΠ (λ Γ* → isSetElU (∣ A∙ ∣ Γ*))) λ δ* → isSetΠ λ Γ* → isProp→isSet (TmSet (π A∙ Γ* (δ* Γ*)) (a [ Γ∙ .π Γ* ]t)))

  _≡ᵗᵗ[_]_ : ∀{Γ∙} → Ty∙ Γ∙ A₁ → A₁ ≡ A₂ → Ty∙ Γ∙ A₂ → Type₁
  _≡ᵗᵗ[_]_ {Γ∙ = Γ∙} a₁ a₁≡a₂ a₂ = PathP (λ i → Ty∙ Γ∙ (a₁≡a₂ i)) a₁ a₂


  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ∙ A∙} → Tm∙ Γ∙ A∙ a₁ → a₁ ≡ a₂ → Tm∙ Γ∙ A∙ a₂ → Type
  _≡ᵗ[_]_ {Γ∙ = Γ∙} {A∙ = A∙} a₁ a₁≡a₂ a₂ = PathP (λ i → Tm∙ Γ∙ A∙ (a₁≡a₂ i)) a₁ a₂
  
  -- Ty-path : {A₁∙ : Ty∙ Γ∙ A₁} {A₂∙ : Ty∙ Γ∙ A₂}{A₁ˢ≡A₂ˢ : A₁ ≡ A₂} → (∀ γ → Ty∙.∣ A₁∙ ∣ γ ≡ Ty∙.∣ A₂∙ ∣ γ ) → A₁∙ ≡ᵗᵗ[ A₁ˢ≡A₂ˢ ] A₂∙ 
  -- ∣ Ty-path path i ∣ = λ a' → path a' i
  -- Ty-path {A₁∙ = A₁∙} {_} {A₁ˢ≡A₂ˢ = A₁ˢ≡A₂ˢ} path i .π Γ* e* = {!   path Γ* i  !} 

  Tm-path : {a₁∙ : Tm∙ Γ∙ A∙ a₁} {a₂∙ : Tm∙ Γ∙ A∙ a₂}{a₁ˢ≡a₂ˢ : a₁ ≡ a₂} → (∀ γ → Tm∙.∣ a₁∙ ∣ γ ≡ Tm∙.∣ a₂∙ ∣ γ ) → a₁∙ ≡ᵗ[ a₁ˢ≡a₂ˢ ] a₂∙ 
  ∣ Tm-path {Γ∙ = Γ∙} {A∙ = A∙} {a₁ = a₁} {a₂ = a₂} {a₁∙ = a₁∙} {a₂∙ = a₂∙} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} path i ∣ Γ* = path Γ* i
  Tm-path {Γ∙ = Γ∙} {A∙ = A∙} {a₁ = a₁} {a₂ = a₂} {a₁∙ = a₁∙} {a₂∙ = a₂∙} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} path i .π Γ* =
    isProp→PathP
    {B = λ i → π A∙ Γ* (path Γ* i) ≡ a₁ˢ≡a₂ˢ i [ Γ∙ .π Γ* ]t} ((λ i₁ → TmSet _ _)) (a₁∙ .π Γ*) (a₂∙ .π Γ*) i
  
  Tm-path' : {a₁∙ : Tm∙ Γ∙ A∙ a₁} {a₂∙ : Tm∙ Γ∙ A∙ a₂}{a₁ˢ≡a₂ˢ : a₁ ≡ a₂} → (∀ γ → Tm∙.∣ a₁∙ ∣ γ ≡ Tm∙.∣ a₂∙ ∣ γ ) → a₁∙ ≡ᵗ[ a₁ˢ≡a₂ˢ ] a₂∙ 
  ∣ Tm-path' {Γ∙ = Γ∙} {A∙ = A∙} {a₁ = a₁} {a₂ = a₂} {a₁∙ = a₁∙} {a₂∙ = a₂∙} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} path i ∣ Γ* = path Γ* i
  Tm-path' {Γ∙ = Γ∙} {A∙ = A∙} {a₁ = a₁} {a₂ = a₂} {a₁∙ = a₁∙} {a₂∙ = a₂∙} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} path i .π Γ* =
    isProp→PathP
    {B = λ i → π A∙ Γ* (path Γ* i) ≡ a₁ˢ≡a₂ˢ i [ Γ∙ .π Γ* ]t} {! ((λ i₁ → TmSet _ _))  !} (a₁∙ .π Γ*) (a₂∙ .π Γ*) i

  ◇∙ :  Con∙ ◇ -- Unit 
  ∣ ◇∙ ∣ = Unit , ((λ tt tt e e' → refl))
  ◇∙ .π = λ tt → ε

  ε∙ : Sub∙ Γ∙ ◇∙ ε
  ∣ ε∙ ∣ = λ x → tt
  ε∙ .π = λ δ* → (sym ◇η)

  infixl 4 _▹∙_ 
  _▹∙_ :  (Γ∙ : Con∙ Γ) → Ty∙ Γ∙ A → Con∙ (Γ ▹ A)
  ∣ Γ∙ ▹∙ A∙ ∣ = Σ (fst Con∙.∣ Γ∙ ∣) (λ Γ* → ElU (∣ A∙ ∣ Γ*)) , isSetΣ (snd ∣ Γ∙ ∣) (λ Γ* → isSetElU (∣ A∙ ∣ Γ*))
  (Γ∙ ▹∙ A∙) .π (Γ* , a*) = Γ∙ .π Γ* ⁺ ∘  ⟨ A∙ .π Γ* a* ⟩ 

  ◇η∙ :  {σ∙ : Sub∙ Γ∙ ◇∙ σ} → σ∙ ≡ˢ[ ◇η ] ε∙
  ◇η∙ {σ∙ } = Sub-path λ δ → refl

  p∙ : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
  ∣ p∙ {Γ∙ = Γ∙} {A∙ = A∙} ∣ (Γ* , _) = Γ*
  p∙ {Γ∙ = Γ∙} {A∙ = A∙} .π (Γ* , A*) = 
    π Γ∙ Γ*   ≡⟨ sym idr ⟩
    π Γ∙ Γ* ∘ id ≡⟨ cong (λ z → π Γ∙ Γ* ∘ z)  (sym p∘⟨⟩) ⟩
    π Γ∙ Γ* ∘ (p ∘ ⟨  A∙ .π Γ* A* ⟩) ≡⟨ sym ass ⟩
    π Γ∙ Γ* ∘ p ∘ ⟨ A∙ .π Γ* A* ⟩ ≡⟨ sym (cong ( λ z → z ∘ ⟨ A∙ .π Γ* A* ⟩) p∘⁺ ) ⟩
    p ∘ π Γ∙ Γ* ⁺ ∘ ⟨ A∙ .π Γ* A* ⟩ ≡⟨ ass ⟩
    p ∘ (Γ∙ .π Γ* ⁺ ∘ ⟨ A∙ .π Γ* A* ⟩) ∎
  
  ⟨_⟩∙ : {t : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ Γ∙ A∙ t → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ t ⟩ 
  ∣ ⟨ a∙ ⟩∙ ∣ Γ* = Γ* , (∣ a∙ ∣ Γ*)
  ⟨_⟩∙ {t = t} {Γ∙ = Γ∙} {A∙ = A∙} a∙ .π  Γ* = 
    Γ∙ .π Γ* ⁺ ∘ ⟨ A∙ .π Γ* (∣ a∙ ∣ Γ*) ⟩  ≡⟨  cong (λ z →  Γ∙ .π Γ* ⁺ ∘ ⟨ z ⟩ ) ( a∙ .π Γ*) ⟩
    Γ∙ .π Γ* ⁺ ∘ ⟨ t [ Γ∙ .π Γ* ]t ⟩  ≡⟨  sym ⟨⟩∘ ⟩
    ⟨ t ⟩ ∘ π Γ∙ Γ* ∎

  p∘⟨⟩∙ : {a∙ : Tm∙ Γ∙ A∙ a} → p∙ ∘∙ ⟨ a∙ ⟩∙ ≡ˢ[ p∘⟨⟩ ] id∙
  p∘⟨⟩∙ = Sub-path λ δ → refl 

  _[_]T∙ : {A : Ty Γ}{γ : Sub Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ} → Ty∙ Γ∙ A → Sub∙ Δ∙ Γ∙ γ → Ty∙ Δ∙ (A [ γ ]T)
  ∣ _[_]T∙ {A = A} {γ = γ} {Δ∙ = Δ∙} {Γ∙ = Γ∙} A∙ γ∙ ∣ Δ* = ∣ A∙ ∣ (∣ γ∙ ∣ Δ*)
  _[_]T∙ {A = A} {γ = γ} {Δ∙ = Δ∙} {Γ∙ = Γ∙} A∙ γ∙ .π Δ* e = subst (Tm ◇) [∘]T (subst (λ z → Tm ◇ (A [ z ]T)) (γ∙ .π Δ*) (A∙ .π (∣ γ∙ ∣ Δ*) e))

  [∘]T∙ : {Δ Γ Θ : Con} {A : Ty Γ} {γ : Sub Δ Γ}{δ : Sub Θ Δ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Θ∙ : Con∙ Θ}{A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ} {δ∙ : Sub∙ Θ∙ Δ∙ δ} → PathP (λ i → Ty∙ Θ∙ ([∘]T {A = A} {γ = γ} {δ = δ} i)) (A∙ [ γ∙ ∘∙ δ∙ ]T∙) ((A∙ [ γ∙ ]T∙) [ δ∙ ]T∙)
  ∣ [∘]T∙ {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙} i ∣ Θ* = ∣ A∙ ∣ (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*))
  [∘]T∙ {Θ = Θ}{A = A} {γ = γ} {δ = δ} {Δ∙ = Δ∙} {Γ∙ = Γ∙}{Θ∙ = Θ∙} {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙} i .π Θ* e = toPathP {A = λ i → Tm ◇ ([∘]T {A = A} {γ = γ} {δ = δ} i [ π Θ∙ Θ* ]T)} {x = left} (sym eq)  i 
    where

    left : Tm ◇ (A [ γ ∘ δ ]T [ π Θ∙ Θ* ]T) 
    left = subst (Tm ◇) [∘]T
         (subst (λ z → Tm ◇ (A [ z ]T))
          (step-≡ (π Γ∙ (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)))
           (step-≡ (γ ∘ Δ∙ .π (∣ δ∙ ∣ Θ*))
            (step-≡ (γ ∘ (δ ∘ Θ∙ .π Θ*)) (γ ∘ δ ∘ π Θ∙ Θ* ∎)
             (λ i₁ → ass {γ = γ}  {δ = δ} {θ = π Θ∙ Θ*} (~ i₁)))
            (λ i₁ → γ ∘ π δ∙ Θ* i₁))
           (π γ∙ (∣ δ∙ ∣ Θ*)))
          (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e))
    right : Tm ◇ (A [ γ ]T [ δ ]T [ π Θ∙ Θ* ]T) 
    right = subst (Tm ◇) [∘]T
         (subst (λ z → Tm ◇ (A [ γ ]T [ z ]T)) (δ∙ .π Θ*)
          (subst (Tm ◇) [∘]T
           (subst (λ z → Tm ◇ (A [ z ]T)) (γ∙ .π (∣ δ∙ ∣ Θ*))
            (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e))))


    eq : right ≡ subst (λ z → Tm ◇ (z [ π Θ∙ Θ* ]T)) [∘]T left
    eq = cong (λ z → subst (Tm ◇) [∘]T
         (subst (λ z → Tm ◇ (A [ γ ]T [ z ]T)) (δ∙ .π Θ*) z)) (sym(substComposite (Tm ◇) (cong (λ z → A [ z ]T) (π γ∙ (∣ δ∙ ∣ Θ*)))  [∘]T (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e))) ∙ cong (subst (Tm ◇) [∘]T)  (sym(substComposite (Tm ◇) ((λ i₁ → A [ π γ∙ (∣ δ∙ ∣ Θ*) i₁ ]T) ∙ [∘]T) (cong (λ z → A [ γ ]T [ z ]T) (π δ∙ Θ*)) (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e))) ∙ sym(substComposite (Tm ◇) (((λ i₁ → A [ π γ∙ (∣ δ∙ ∣ Θ*) i₁ ]T) ∙ [∘]T) ∙ (λ i₁ → A [ γ ]T [ π δ∙ Θ* i₁ ]T)) [∘]T (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e)) 
         ∙  sym (cong (subst (λ z → Tm ◇ (z [ π Θ∙ Θ* ]T)) [∘]T) (sym( substComposite  (Tm ◇) (cong (λ z → A [ z ]T) ((step-≡ (π Γ∙ (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*))) -- left
           (step-≡ (γ ∘ Δ∙ .π (∣ δ∙ ∣ Θ*))
            (step-≡ (γ ∘ (δ ∘ Θ∙ .π Θ*)) (γ ∘ δ ∘ π Θ∙ Θ* ∎)
             (λ i₁ → ass  {γ = γ}  {δ = δ} {θ = π Θ∙ Θ*} (~ i₁)))
            (λ i₁ → γ ∘ π δ∙ Θ* i₁))
           (π γ∙ (∣ δ∙ ∣ Θ*))))) [∘]T (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e)))  ∙ sym(substComposite (Tm ◇) ((λ i₁ →
           A [
           step-≡ (π Γ∙ (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)))
           (step-≡ (γ ∘ Δ∙ .π (∣ δ∙ ∣ Θ*))
            (step-≡ (γ ∘ (δ ∘ Θ∙ .π Θ*)) (γ ∘ δ ∘ π Θ∙ Θ* ∎)
             (λ i₂ → ass {γ = γ}  {δ = δ} {θ = π Θ∙ Θ*} (~ i₂)))
            (λ i₂ → γ ∘ π δ∙ Θ* i₂))
           (π γ∙ (∣ δ∙ ∣ Θ*)) i₁
           ]T)
        ∙ [∘]T) (cong (λ z → z [ π Θ∙ Θ* ]T) [∘]T)  (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e)) ∙  (cong (λ z → subst (Tm ◇) z (A∙ .π (∣ γ∙ ∣ (∣ δ∙ ∣ Θ*)) e)) (TySet _ _ _ _)))  
  [id]T∙ :  {Γ : Con} {A : Ty Γ} {Γ∙ : Con∙ Γ} {A∙ : Ty∙ Γ∙ A} → PathP (λ i → Ty∙ Γ∙ ([id]T {A = A} i)) (A∙ [ id∙ ]T∙) A∙
  ∣ [id]T∙ {Γ = Γ} {A = A} {Γ∙ = Γ∙} {A∙ = A∙} i ∣ Γ* = ∣ A∙ ∣ Γ*
  [id]T∙ {Γ = Γ} {A = A} {Γ∙ = Γ∙} {A∙ = A∙} i .π  Γ* eΓ* =  toPathP {A =  λ i → Tm ◇ ([id]T i [ π Γ∙ Γ* ]T)} {x = left} eq i 
    where 
    left : Tm ◇ (A [ id ]T [ π Γ∙ Γ* ]T)
    left = subst (Tm ◇) [∘]T
         (subst (λ z → Tm ◇ (A [ z ]T)) (λ i₁ → idl {γ = π Γ∙ Γ*} (~ i₁)) (A∙ .π Γ* eΓ*))
    eq :  subst (λ z → Tm ◇ (z [ π Γ∙ Γ* ]T)) ([id]T {A = A}) left ≡ A∙ .π Γ* eΓ*  
    eq = cong (subst (λ z → Tm ◇ (z [ π Γ∙ Γ* ]T)) ([id]T {A = A})) 
            (sym (substComposite (Tm ◇) (cong (λ z → A [ z ]T) (sym (idl {γ = π Γ∙ Γ*}))) [∘]T (A∙ .π Γ* eΓ*))) 
            ∙ sym (substComposite (Tm ◇) ((λ i₁ → A [ idl {γ = π Γ∙ Γ*} (~ i₁) ]T) ∙ [∘]T) (cong (λ z → z [ π Γ∙ Γ* ]T) ([id]T {A = A})) (A∙ .π Γ* eΓ*)) 
            ∙ {! subst (Tm ◇) refl (A∙ .π Γ* eΓ*)  !} --cong (λ z → subst (Tm ◇) z (A∙ .π Γ* eΓ*)) (TySet _ _ _ _) 
            ∙ substRefl  {B = (Tm ◇)} {x = (A [ π Γ∙ Γ* ]T)} (A∙ .π Γ* eΓ*)


  [p][⟨⟩]T∙ : {Γ : Con} {A B : Ty Γ} {b : Tm Γ B} {Γ∙ : Con∙ Γ}  {A∙ : Ty∙ Γ∙ A} {B∙ : Ty∙ Γ∙ B}  {b∙ : Tm∙ Γ∙ B∙ b} →  PathP (λ i → Ty∙ Γ∙ ([p][⟨⟩]T {A = A} {b = b} i))  ((A∙ [ p∙ ]T∙) [ ⟨ b∙ ⟩∙ ]T∙)  A∙
  ∣ [p][⟨⟩]T∙ {Γ = Γ} {A = A} {B = B} {b = b} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙} {b∙ = b∙} i ∣ Γ* = ∣ A∙ ∣ Γ*
  [p][⟨⟩]T∙ {Γ = Γ} {A = A} {B = B} {b = b} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙} {b∙ = b∙} i .π Γ* eΓ* = toPathP {A =  λ i →  Tm ◇ ([p][⟨⟩]T {A = A} {b = b} i [ π Γ∙ Γ* ]T)} {x = left} eq i
    where 
    p4 : π Γ∙ Γ* ≡ p ∘ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩) 
    p4 = (step-≡ (π Γ∙ Γ*)
             (step-≡ (π Γ∙ Γ* ∘ id)
              (step-≡ (π Γ∙ Γ* ∘ (p ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩))
               (step-≡ (π Γ∙ Γ* ∘ p ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩)
                (step-≡ (p ∘ π Γ∙ Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩)
                 (p ∘ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩) ∎) ass)
                (λ i₁ → p∘⁺ (~ i₁) ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩))
               (λ i₁ → ass  {γ = π Γ∙ Γ*}  {δ = p} {θ = ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩}   (~ i₁)))
              (λ i₁ → π Γ∙ Γ* ∘ p∘⟨⟩ {a = B∙ .π Γ* (∣ b∙ ∣ Γ*)} (~ i₁)))
             (λ i₁ → idr {γ = π Γ∙ Γ*} (~ i₁)))
    left : Tm ◇ (A [ p ]T [ ⟨ b ⟩ ]T [ π Γ∙ Γ* ]T) -- Tm ◇ (A [ π Γ∙ Γ* ]T)
    left = subst (Tm ◇) [∘]T
         (subst (λ z → Tm ◇ (A [ p ]T [ z ]T))
          (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩)
           (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ b [ Γ∙ .π Γ* ]t ⟩) (⟨ b ⟩ ∘ π Γ∙ Γ* ∎)
            (λ i₁ → ⟨⟩∘ {a = b}{γ = π Γ∙ Γ*} (~ i₁)))
           (λ i₁ → Γ∙ .π Γ* ⁺ ∘ ⟨ b∙ .π Γ* i₁ ⟩))
          (subst (Tm ◇) [∘]T
           (subst (λ z → Tm ◇ (A [ z ]T))
            p4
            (A∙ .π Γ* eΓ*))))
    eq : subst (λ z → Tm ◇ (z [ π Γ∙ Γ* ]T)) ([p][⟨⟩]T {A = A} {b = b}) left ≡ A∙ .π Γ* eΓ*  
    eq = cong  (λ  z → subst (λ z → Tm ◇ (z [ π Γ∙ Γ* ]T)) ([p][⟨⟩]T {A = A} {b = b}) (subst (Tm ◇) [∘]T
         (subst (λ z → Tm ◇ (A [ p ]T [ z ]T))
          (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩)
           (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ b [ Γ∙ .π Γ* ]t ⟩) (⟨ b ⟩ ∘ π Γ∙ Γ* ∎)
            (λ i₁ → ⟨⟩∘ {a = b}{γ = π Γ∙ Γ*} (~ i₁)))
           (λ i₁ → Γ∙ .π Γ* ⁺ ∘ ⟨ b∙ .π Γ* i₁ ⟩))
          z))) (sym (substComposite (Tm ◇) (cong (λ z → A [ z ]T) p4) [∘]T ((A∙ .π Γ* eΓ*)))) ∙ cong (λ z → subst (λ z → Tm ◇ (z [ π Γ∙ Γ* ]T)) [p][⟨⟩]T (subst (Tm ◇) [∘]T z ))  (sym (substComposite  (Tm ◇) ((λ i₁ → A [ p4 i₁ ]T) ∙ [∘]T) (cong (λ z → A [ p ]T [ z ]T) ((step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩) (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ b [ Γ∙ .π Γ* ]t ⟩) (⟨ b ⟩ ∘ π Γ∙ Γ* ∎)   (λ i₁ → ⟨⟩∘ {a = b}{γ = π Γ∙ Γ*} (~ i₁)))   (λ i₁ → Γ∙ .π Γ* ⁺ ∘ ⟨ b∙ .π Γ* i₁ ⟩)))) (A∙ .π Γ* eΓ*))) ∙ cong (subst (λ z → Tm ◇ (z [ π Γ∙ Γ* ]T)) [p][⟨⟩]T) (sym (substComposite (Tm ◇)  (((λ i₁ → A [ p4 i₁ ]T) ∙ [∘]T) ∙
         (λ i₁ →
            A [ p ]T [
            step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩)
            (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ b [ Γ∙ .π Γ* ]t ⟩) (⟨ b ⟩ ∘ π Γ∙ Γ* ∎)
             (λ i₂ → ⟨⟩∘ {a = b}{γ = π Γ∙ Γ*} (~ i₂)))
            (λ i₂ → Γ∙ .π Γ* ⁺ ∘ ⟨ b∙ .π Γ* i₂ ⟩) i₁
            ]T)) [∘]T  (A∙ .π Γ* eΓ*))) ∙ sym (substComposite (Tm ◇)  ((((λ i₁ → A [ p4 i₁ ]T) ∙ [∘]T) ∙
         (λ i₁ →
            A [ p ]T [
            step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ B∙ .π Γ* (∣ b∙ ∣ Γ*) ⟩)
            (step-≡ (Γ∙ .π Γ* ⁺ ∘ ⟨ b [ Γ∙ .π Γ* ]t ⟩) (⟨ b ⟩ ∘ π Γ∙ Γ* ∎)
             (λ i₂ → ⟨⟩∘ {a = b}{γ = π Γ∙ Γ*} (~ i₂)))
            (λ i₂ → Γ∙ .π Γ* ⁺ ∘ ⟨ b∙ .π Γ* i₂ ⟩) i₁
            ]T))
        ∙ [∘]T) (cong (λ z → z [ π Γ∙ Γ* ]T ) ([p][⟨⟩]T {A = A} {b = b}))  (A∙ .π Γ* eΓ*))  ∙ cong (λ z → subst (Tm ◇) z (A∙ .π Γ* eΓ*)) (TySet _ _ _ _)  ∙ substRefl  {B = (Tm ◇)} {x = (A [ π Γ∙ Γ* ]T)} (A∙ .π Γ* eΓ*) --substRefl  {B = (Tm ◇)} {x = (A [ π Γ∙ Γ* ]T)} (A∙ .π Γ* eΓ*)

  U∙ : {Γ : Con} {Γ∙ : Con∙ Γ} → Ty∙ Γ∙ U
  ∣ U∙ ∣ = λ _ → ⊥U
  U∙ .π  Γ* b = exfalso b

  U[]∙ :  {Δ Γ : Con} {γ : Sub Δ Γ} {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ} {γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Ty∙ Δ∙ (U[] {γ = γ} i)) (U∙ [ γ∙ ]T∙) U∙
  ∣ U[]∙ i ∣ Δ* = ⊥U
  U[]∙ {γ = γ}{Δ∙ = Δ∙}{Γ∙ = Γ∙}{γ∙ = γ∙} i .π Δ* b = toPathP {A =  λ i → Tm ◇ ((U[] {γ = γ} i) [  π Δ∙ Δ* ]T)} {x = left} eq i 
    where 
      left : Tm ◇ (U [ γ ]T [ π Δ∙ Δ* ]T)
      left = subst (Tm ◇) [∘]T (subst (λ z → Tm ◇ (U [ z ]T)) (γ∙ .π Δ*) (exfalso b))
      eq : subst (λ z → Tm ◇ (z [ π Δ∙ Δ* ]T)) (U[] {γ = γ}) left  ≡ exfalso b 
      eq = cong (subst (λ z → Tm ◇ (z [ π Δ∙ Δ* ]T)) U[]) (sym (substComposite  (Tm ◇) (cong (λ z → (U [ z ]T)) (π γ∙ Δ*)) [∘]T  (exfalso b)))  ∙ sym (substComposite  (Tm ◇) ((λ i₁ → U [ γ∙ .π Δ* i₁ ]T) ∙ [∘]T) (cong  (λ z → z [ π Δ∙ Δ* ]T) (U[] {γ = γ})) (exfalso b)) ∙  -- {!  cong (λ z → subst (Tm ◇) z (exfalso b)) (TySet _ _ _ _) !} -- Tm ◇ (U [ π Δ∙ Δ* ]T)
          {!   !} --congS {x = λ i₁ → (((λ i₂ → U [ γ∙ .π Δ* i₂ ]T) ∙ [∘]T) ∙  (λ i₂ → U[] {γ = γ} i₂ [ π Δ∙ Δ* ]T))  i₁}{y = cong (λ z → U [ z ]T) (π γ∙ Δ*)  ∙ [∘]T {A = U}{γ = γ}{δ = π Δ∙ Δ*} ∙ cong (λ z → z [ π Δ∙ Δ* ]T ) (U[] {γ = γ})} (λ z → subst (Tm ◇) z (exfalso b)) {! (TySet _ _ _ _)  !} -- congS (λ z → subst (Tm ◇) z (exfalso b)) (TySet _ _ _ _)  
           ∙ (exfalso b) 

  El∙ :  {Γ : Con} {Â : Tm Γ U} {Γ∙ : Con∙ Γ} → Tm∙ Γ∙ U∙ Â → Ty∙ Γ∙ (El Â)
  ∣ El∙ a ∣ = λ Γ' → ⊥U
  El∙ a .π Γ* b = exfalso b

  Π∙ : {Γ : Con} {A : Ty Γ} {B : Ty (Γ ▹ A)}{Γ∙ : Con∙ Γ} (A∙ : Ty∙ Γ∙ A) →  Ty∙ (Γ∙ ▹∙ A∙) B → Ty∙ Γ∙ (Π A B)                                                                                                                                                                                                                                     
  ∣ Π∙ {Γ = Γ} {A = A} {B = B} {Γ∙ = Γ∙} A∙ B∙ ∣ Γ* = ΣU (TmU ◇ (Π A B [ π Γ∙ Γ* ]T)) λ ab → ΣU (ΠU (∣ A∙ ∣  Γ*) (λ Ea → ∣ B∙ ∣ (Γ* , Ea))) λ m → ΠU (∣ A∙ ∣  Γ*) λ eA → PathU {A₁ = TmU ◇ (B [ Γ∙ .π Γ* ⁺ ]T [ ⟨ A∙ .π Γ* eA ⟩ ]T)} (subst (Tm ◇) ([∘]T) (π B∙  (Γ* , eA) (m eA))) (app ((subst (Tm ◇) (Π[] {A = A}) ab)) (π A∙ Γ* eA)) 
  Π∙ {Γ = Γ} {A = A} {B = B} {Γ∙ = Γ∙} A∙ B∙ .π Γ* eA = fst eA


  _[_]t∙ : {Δ Γ : Con} {A : Ty Γ} {a : Tm Γ A} {γ : Sub Δ Γ}{Δ∙ : Con∙ Δ} {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ Γ∙ A∙ a → (γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
  ∣ a∙ [ γ∙ ]t∙ ∣ γ* = ∣ a∙ ∣  (∣ γ∙ ∣ γ*)
  (_[_]t∙ {A = A} {a = a} {γ = γ}{Δ∙ = Δ∙}{Γ∙ = Γ∙}{A∙ = A∙} a∙ γ∙ ) .π Δ* =  sym(substComposite (Tm ◇) (cong (λ z → A [ z ]T) (π γ∙ Δ*)) [∘]T  (A∙ .π (∣ γ∙ ∣ Δ*) (∣ a∙ ∣ (∣ γ∙ ∣ Δ*))))  ∙ cong (subst (Tm ◇) ((λ i → A [ π γ∙ Δ* i ]T) ∙ [∘]T)) (π a∙ (∣ γ∙ ∣ Δ*))  ∙ {!   !}


  q∙ : {Γ : Con} {A : Ty Γ} {Γ∙ : Con∙ Γ} {A∙ : Ty∙ Γ∙ A} → Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ ]T∙) q 
  ∣ q∙ ∣ (Γ* , eΓ) =  eΓ
  q∙ {Γ = Γ}{A = A}{Γ∙ = Γ∙}{A∙ = A∙} .π (Γ* , eΓ) = sym (substComposite (Tm ◇) (cong (λ z → A [ z ]T) q2) [∘]T (A∙ .π Γ* eΓ)) ∙  sym {! ? ∙  fromPathP ([∘]t {γ = Γ∙ .π Γ* ⁺}{δ = ⟨ A∙ .π Γ* eΓ ⟩}{a = q}) ∙ ?!}
    where 
      q2 : π Γ∙ Γ* ≡ p ∘ (Γ∙ .π Γ* ⁺ ∘ ⟨ A∙ .π Γ* eΓ ⟩)
      q2 = (step-≡ (π Γ∙ Γ*)
        (step-≡ (π Γ∙ Γ* ∘ id)
         (step-≡ (π Γ∙ Γ* ∘ (p ∘ ⟨ A∙ .π Γ* eΓ ⟩))
          (step-≡ (π Γ∙ Γ* ∘ p ∘ ⟨ A∙ .π Γ* eΓ ⟩)
           (step-≡ (p ∘ π Γ∙ Γ* ⁺ ∘ ⟨ A∙ .π Γ* eΓ ⟩)
            (p ∘ (Γ∙ .π Γ* ⁺ ∘ ⟨ A∙ .π Γ* eΓ ⟩) ∎) ass)
           (λ i → p∘⁺ (~ i) ∘ ⟨ A∙ .π Γ* eΓ ⟩))
          (λ i → ass (~ i)))
         (λ i → π Γ∙ Γ* ∘ p∘⟨⟩ (~ i)))
        (λ i → idr (~ i)))
      eq : q [ Γ∙ .π Γ* ⁺ ∘ ⟨ A∙ .π Γ* eΓ ⟩ ]t ≡ subst (Tm ◇) ((λ i → A [ q2 i ]T) ∙ [∘]T) (A∙ .π Γ* eΓ) --A∙ .π Γ* eΓ
      eq = fromPathP⁻  ([∘]t {γ = Γ∙ .π Γ* ⁺}{δ = ⟨ A∙ .π Γ* eΓ ⟩}{a = q}) ∙ substComposite _ _ _ (q [ Γ∙ .π Γ* ⁺ ]t [ ⟨ A∙ .π Γ* eΓ ⟩ ]t) ∙   fromPathP (cong (λ z →  (transport⁻ (λ i → Tm ◇ ([∘]T i))(z [ ⟨ A∙ .π Γ* eΓ ⟩ ]t))) (fromPathP⁻ (q[⁺] {γ = Γ∙ .π Γ* } ))) ∙ {!   !} --substComposite {!   !} {!   !} {!   !}  (q [ Γ∙ .π Γ* ⁺ ]t [ ⟨ A∙ .π Γ* eΓ ⟩ ]t) ∙ fromPathP (cong (λ z →  (transport⁻ (λ i → Tm ◇ ([∘]T i))(z [ ⟨ A∙ .π Γ* eΓ ⟩ ]t))) (fromPathP⁻ (q[⁺] {γ = Γ∙ .π Γ* } )))  ∙ {!   !} -- q[⁺] {γ = Γ∙ .π Γ* ⁺ } -- fromPathP⁻ (q[⁺] {γ = Γ∙ .π Γ* } )
open import mltt-minimal.DepModel as D

Canons : D.DepModel 
Canons = 
    record
  { Con∙ = Canonicity.Con∙
  ; Sub∙ = Canonicity.Sub∙
  ; Ty∙ = Canonicity.Ty∙
  ; Tm∙ = Canonicity.Tm∙
  ; _▹∙_ = Canonicity._▹∙_
  ; ◇∙ = Canonicity.◇∙
  ; SubSet∙ = Canonicity.SubSet∙
  ; TySet∙ = Canonicity.TySet∙ 
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
  ; _[_]T∙ = Canonicity._[_]T∙
  ; [∘]T∙ = Canonicity.[∘]T∙
  ; [id]T∙ = Canonicity.[id]T∙
  ; [p][⟨⟩]T∙ = Canonicity.[p][⟨⟩]T∙
  ; U∙ = Canonicity.U∙
  ; U[]∙ = Canonicity.U[]∙
  ; El∙ = Canonicity.El∙
  ; Π∙ = Canonicity.Π∙
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
