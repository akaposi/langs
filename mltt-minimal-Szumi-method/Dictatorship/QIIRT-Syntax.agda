{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections #-}

module Dictatorship.QIIRT-Syntax where

open import Lib
open import Dictatorship.Syntax
open import Dictatorship.DepModel
open I
{-
open Sorts∙
open CwF∙
open Sigma∙
open Pi∙
open Empty∙
open BoolT∙
-}

private variable
  Γ Δ Θ Ξ Ω : Con
  γ δ θ ξ : Sub Δ Γ
  A B C : Ty Γ
  a b c : Tm Γ A

module QIIRT-Sorts where

  record Con∙ (Γ : Con) : Set where
    field
      instance ∣_∣ : L.⊤

  mkCon∙ : ∀ Γ → Con∙ Γ
  mkCon∙ _ = _

  record Sub∙ {Δ}{Γ}(Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) : Set where
    field
      ∣_∣ : {Θ : Con}(δ : Sub Θ Δ) → ∃[ θ ] γ ∘ δ ≈ θ

    ∣_∣Subₑ = λ Θ δ → ∣_∣ {Θ} δ

  Sub∙ₑ = λ Δ Γ Δ∙ Γ∙ γ → Sub∙ {Δ} {Γ} Δ∙ Γ∙ γ

  mkSub∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}(γ : Sub Δ Γ) → ((Θ : Con)(δ : Sub Θ Δ) → ∃[ θ ] γ ∘ δ ≈ θ) → Sub∙ Δ∙ Γ∙ γ
  mkSub∙ _ f = Sub∙.constructor (λ {x} → f x)

  mkSub∙ₑ : ∀ Δ Γ → (Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → ((Θ : Con)(δ : Sub Θ Δ) → ∃[ θ ] γ ∘ δ ≈ θ) → Sub∙ Δ∙ Γ∙ γ
  mkSub∙ₑ _ _ _ _ _ f = Sub∙.constructor (λ {x} → f x)

  record Ty∙ {Γ}(Γ∙ : Con∙ Γ)(A : Ty Γ) : Set where
    field
      ∣_∣ : {Δ : Con}(γ : Sub Δ Γ) → ∃[ A[γ]T ] A [ γ ]T ≈ A[γ]T

    ∣_∣Tyₑ = λ Δ γ → ∣_∣ {Δ} γ

  Ty∙ₑ = λ Γ Γ∙ A → Ty∙ {Γ} Γ∙ A

  mkTy∙ : ∀{Γ}{Γ∙ : Con∙ Γ}(A : Ty Γ) → (∀ Δ → (γ : Sub Δ Γ) → ∃[ A[γ]T ] A [ γ ]T ≈ A[γ]T) → Ty∙ Γ∙ A
  mkTy∙ _ f = Ty∙.constructor (λ {x} → f x)

  mkTy∙ₑ : ∀ Γ → (Γ∙ : Con∙ Γ)(A : Ty Γ) → (∀ Δ → (γ : Sub Δ Γ) → ∃[ A[γ]T ] A [ γ ]T ≈ A[γ]T) → Ty∙ Γ∙ A
  mkTy∙ₑ _ _ A f = Ty∙.constructor (λ {x} → f x)
  
  record Tm∙ {Γ}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A)(a : Tm Γ A) : Set where
    field
      ∣_∣ : {Δ : Con}(γ : Sub Δ Γ) → let (A[γ]T ,-) = Ty∙.∣ A∙ ∣ γ in ∃[ a[γ]t ∶ Tm Δ A[γ]T ] a [ γ ]t ~[ cong (Tm _) $ un ] a[γ]t

    ∣_∣Tmₑ = λ Δ γ → ∣_∣ {Δ} γ

  Tm∙ₑ = λ Γ A Γ∙ A∙ a → Tm∙ {Γ} {A} Γ∙ A∙ a
  
  mkTm∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(a : Tm Γ A) → (∀ Δ → (γ : Sub Δ Γ) → let (A[γ]T ,-) = Ty∙.∣ A∙ ∣ γ in ∃[ a[γ]t ∶ Tm Δ A[γ]T ] a [ γ ]t ~[ cong (Tm _) $ un ] a[γ]t) → Tm∙ Γ∙ A∙ a
  mkTm∙ _ _ f = Tm∙.constructor (λ {x} → f x)

  mkTm∙ₑ : ∀ Γ → (A : Ty Γ)(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A)(a : Tm Γ A) → (∀ Δ → (γ : Sub Δ Γ) → let (A[γ]T ,-) = Ty∙.∣ A∙ ∣ γ in ∃[ a[γ]t ∶ Tm Δ A[γ]T ] a [ γ ]t ~[ cong (Tm _) $ un ] a[γ]t) → Tm∙ Γ∙ A∙ a
  mkTm∙ₑ _ _ _ _ _ f = Tm∙.constructor (λ {x} → f x)
  
  open Con∙ public
  open Sub∙ public
  open Ty∙ public
  open Tm∙ public

  infixl 8 _∘∙_
  infixl 5 _▹∙_
  infixl 9 _[_]T∙ _[_]t∙
  infixl 10 _⁺∙
  infixl 11 ⟨_⟩∙
  infixr 5 _,∙_

  _∘∙_ : {Δ : Con} {Δ∙ : Con∙ Δ} {Γ : Con} {Γ∙ : Con∙ Γ}
         {γ : Sub Δ Γ} {Θ : Con} {Θ∙ : Con∙ Θ} {δ : Sub Θ Δ} →
         Sub∙ Δ∙ Γ∙ γ → Sub∙ Θ∙ Δ∙ δ → Sub∙ Θ∙ Γ∙ (γ ∘ δ)
  _∘∙_ {γ = γ} {δ = δ} γ∙ δ∙ = Sub∙.constructor λ θ
                             → let (δ∘θ ,ₚ e1) = ∣ δ∙ ∣ θ
                                   (γ∘δ∘θ ,ₚ e2) = ∣ γ∙ ∣ δ∘θ
                               in γ∘δ∘θ ,ₚ ass ∙ cong (γ ∘_) $ e1 ∙ e2

  ass∙ : {Δ Γ : Con} {Δ∙ : Con∙ Δ} {Γ∙ : Con∙ Γ}
         {γ : Sub Δ Γ} {γ∙ : Sub∙ Δ∙ Γ∙ γ} {Θ : Con}
         {Θ∙ : Con∙ Θ} {δ : Sub Θ Δ}
         {δ∙ : Sub∙ Θ∙ Δ∙ δ} {Ξ : Con} {Ξ∙ : Con∙ Ξ}
         {θ : Sub Ξ Θ} {θ∙ : Sub∙ Ξ∙ Θ∙ θ}
       → (γ∙ ∘∙ δ∙) ∘∙ θ∙ ~[ cong (Sub∙ _ _) $ ass ] γ∙ ∘∙ (δ∙ ∘∙ θ∙)
  ass∙ {Δ} {Γ} {Δ∙} {Γ∙} {γ = γ} {γ∙} {Θ} {Θ∙} {δ = δ} {δ∙} {Ξ} {Ξ∙} {θ = θ} {θ∙} = 
    cong mkSub∙ $ ass $ funext λ {Χ} {_} → λ {refl → funext λ {χ} {_} → λ {refl →
    let (θ∘χ ,ₚ ≈θ∘χ) = ∣ θ∙ ∣ χ
        (δ∘[θ∘χ] ,ₚ ≈δ∘[θ∘χ]) = ∣ δ∙ ∣ θ∘χ
        (γ∘[δ∘[θ∘χ]] ,ₚ ≈γ∘[δ∘[θ∘χ]]) = ∣ γ∙ ∣ δ∘[θ∘χ]
    in Σ-extₚ refl (funext λ {χ'} {_} → λ {refl → cong (_≈ χ') $ (cong (_∘ χ) $ ass)})}}

  id∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Sub∙ Γ∙ Γ∙ id
  id∙ = Sub∙.constructor λ δ → δ ,ₚ idl

  idl∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → id∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ idl ] γ∙
  idl∙ {γ∙ = γ∙} = cong mkSub∙ $ idl $ funext λ {Θ} → λ {refl → funext λ {θ} → λ {refl →
    let
      (γ∘θ ,ₚ ≈γ∘θ) = ∣ γ∙ ∣ θ
    in Σ-extₚ refl (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ θ) $ idl)})}}

  idr∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → γ∙ ∘∙ id∙ ~[ cong (Sub∙ _ _) $ idr ] γ∙
  idr∙ {γ∙ = γ∙} = cong mkSub∙ $ idr $ funext λ {Θ} → λ {refl → funext λ {θ} → λ {refl →
    let
      (γ∘θ ,ₚ ≈γ∘θ) = ∣ γ∙ ∣ θ
    in Σ-extₚ refl (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ θ) $ idr)})}}

  ◇∙ : Con∙ ◇
  ◇∙ = _

  ε∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Sub∙ Γ∙ ◇∙ ε
  ε∙ = Sub∙.constructor λ δ → ε ,ₚ ◇η

  ◇η∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{γ : Sub Γ ◇}{γ∙ : Sub∙ Γ∙ ◇∙ γ} → γ∙ ~[ cong (Sub∙ _ _) $ ◇η ] ε∙
  ◇η∙ {γ∙ = γ∙} = cong mkSub∙ $ ◇η $ funext λ {Θ} → λ {refl → funext λ {δ} → λ {refl →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    in Σ-extₚ ◇η (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ δ) $ ◇η)})}}
  
  _[_]T∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{γ : Sub Δ Γ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Ty∙ Δ∙ (A [ γ ]T)
  _[_]T∙ {A = A} {γ} A∙ γ∙ = Ty∙.constructor λ {Θ} δ → 
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    in A [ γ∘δ ]T ,ₚ sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ

  []T∙ₑ = λ Δ Γ A Δ∙ Γ∙ A∙ γ γ∙ → _[_]T∙ {Γ} {Δ} {Γ∙} {Δ∙} {A} {γ} A∙ γ∙
  
  [∘]T∙ : ∀{Γ Δ Θ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A : Ty Γ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}
          {A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}
        → A∙ [ γ∙ ∘∙ δ∙ ]T∙ ~[ cong (Ty∙ _) $ [∘]T ] A∙ [ γ∙ ]T∙ [ δ∙ ]T∙
  [∘]T∙ {A = A} {γ∙ = γ∙} {δ∙} = cong mkTy∙ $ [∘]T $ funext λ {Ξ} → λ {refl → funext λ {θ} → λ {refl →
    let
      (δ∘θ ,ₚ ≈δ∘θ) = ∣ δ∙ ∣ θ
      (γ∘[δ∘θ] ,ₚ ≈γ∘[δ∘θ]) = ∣ γ∙ ∣ δ∘θ
    in Σ-extₚ (cong (A [_]T) $ sym ≈γ∘[δ∘θ] ∙ [∘]T) (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_[ θ ]T) $ [∘]T)})}}
  
  [id]T∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
         → A∙ [ id∙ ]T∙ ~[ cong (Ty∙ _) $ [id]T ] A∙
  [id]T∙ {A∙ = A∙} = cong mkTy∙ $ [id]T $ funext λ {Δ} → λ {refl → funext λ {γ} → λ {refl →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
    in Σ-extₚ ≈A[γ]T (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_[ γ ]T) $ [id]T)})}}
  
  _[_]t∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{a : Tm Γ A}{γ : Sub Δ Γ}
           {A∙ : Ty∙ Γ∙ A}(a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ)
         → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
  _[_]t∙ {a = a} {γ} {A∙} a∙ γ∙ = Tm∙.constructor λ {Θ} δ →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    in a [ γ∘δ ]t ,ₚ sym [∘]t ∙ cong (a [_]t) $ ≈γ∘δ

  [∘]t∙ : ∀{Γ Δ Θ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A : Ty Γ}{a : Tm Γ A}{γ : Sub Δ Γ}{δ : Sub Θ Δ}
          {A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}
        → a∙ [ γ∙ ∘∙ δ∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Θ∙) $ [∘]T $ [∘]T∙ {A∙ = A∙} {γ∙} {δ∙} $ [∘]t ] a∙ [ γ∙ ]t∙ [ δ∙ ]t∙
  [∘]t∙ {A = A} {a} {γ} {δ} {A∙} {a∙} {γ∙} {δ∙} = cong (mkTm∙ₑ _) $ [∘]T $ refl $ [∘]T∙ {A∙ = A∙} {γ∙} {δ∙} $ [∘]t $ funext λ {Ξ} → λ {refl → funext λ {θ} → λ {refl →
    let
      (δ∘θ ,ₚ ≈δ∘θ) = ∣ δ∙ ∣ θ
      (γ∘[δ∘θ] ,ₚ ≈γ∘[δ∘θ]) = ∣ γ∙ ∣ δ∘θ
    in Σ-extₚ (cong (a [_]t) $ sym ≈γ∘[δ∘θ] ∙ [∘]t) (funextₕ (cong (Tm Ξ) $ (cong (A [_]T) $ sym ≈γ∘[δ∘θ] ∙ [∘]T)) λ {ξ} {ξ'} e → cong ~ₑ $ (cong (Tm Ξ) $ (cong _[ θ ]T $ [∘]T)) $ (cong ([]tₑ _ _) $ [∘]T $ [∘]t $ refl) $ (cong (Tm Ξ) $ (cong (A [_]T) $ sym ≈γ∘[δ∘θ] ∙ [∘]T)) $ e)}}
  
  [id]t∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}
         → a∙ [ id∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Γ∙) $ [id]T $ [id]T∙ $ [id]t ] a∙
  [id]t∙ {A = A} {A∙} {a} {a∙} = cong (mkTm∙ₑ _) $ [id]T $ refl $ [id]T∙ $ [id]t $ funext λ {Δ} → λ {refl → funext λ {γ} → λ {refl →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    in Σ-extₚ ≈a[γ]t (funextₕ (cong (Tm Δ) $ ≈A[γ]T) λ {z} e → cong ~ₑ $ (cong (Tm Δ) $ (cong _[ γ ]T $ [id]T)) $ (cong ([]tₑ _ _) $ [id]T $ [id]t $ refl) $ (cong (Tm Δ) $ ≈A[γ]T) $ e)}}
  
  _▹∙_ : ∀{Γ}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A) → Con∙ (Γ ▹ A)
  _▹∙_ _ _ = _
  
  p∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
  p∙ = Sub∙.constructor (λ {Δ} γ → p ∘ γ ,ₚ refl)
  
  q∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ {A∙ = A∙} ]T∙) q
  q∙ {A∙ = A∙} = Tm∙.constructor λ {Δ} γ → coe (cong (Tm _) $ sym [∘]T) (q [ γ ]t) ,ₚ coh
  
  _⁺∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{γ : Sub Δ Γ}(γ∙ : Sub∙ Δ∙ Γ∙ γ)
      → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) (Γ∙ ▹∙ A∙) (γ ⁺)
  _⁺∙ {A∙ = A∙} {γ} γ∙ = Sub∙.constructor λ {Θ} δ → γ ⁺ ∘ δ ,ₚ refl
  
  ∘⁺∙ : ∀{Γ Δ Θ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A : Ty Γ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}
        {A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}
      → _⁺∙ {A∙ = A∙} (γ∙ ∘∙ δ∙) ~[ cong Sub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Θ∙) $ [∘]T $ [∘]T∙ {A∙ = A∙} {γ∙} {δ∙}) $ cong (Γ∙ ▹∙ A∙) $ ∘⁺ ] _⁺∙ {A∙ = A∙} γ∙ ∘∙ _⁺∙ {A∙ = A∙ [ γ∙ ]T∙} δ∙
  ∘⁺∙ {Θ = Θ} {A = A} {γ} {δ} {A∙} {γ∙} {δ∙} = cong mkSub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ refl $ (cong mkCon∙ $ (cong (Θ ▹_) $ [∘]T)) $ refl $ ∘⁺ $ funext λ {Ξ} → λ {refl → funextₕ (cong (Sub Ξ) $ (cong (Θ ▹_) $ [∘]T)) λ {θ} {θ'} e →
    Σ-extₚ (cong (∘ₑ _) $ (cong (Θ ▹_) $ [∘]T) $ refl $ ∘⁺ $ e ∙ ass) (funext λ {z} → λ {refl → cong ~ₑ $ refl $ (cong (∘ₑ _) $ (cong (Θ ▹_) $ [∘]T) $ refl $ ∘⁺ $ e) $ refl $ refl})}
  
  id⁺∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
       → _⁺∙ {A∙ = A∙} id∙ ~[ cong Sub∙ₑ $ (cong (Γ ▹_) $ [id]T) $ cong (Γ ▹ A) $ (cong mkCon∙ $ (cong (Γ ▹_) $ [id]T)) $ cong (Γ∙ ▹∙ A∙) $ id⁺ ] id∙
  id⁺∙ {A = A} {A∙} = cong mkSub∙ₑ $ (cong (_ ▹_) $ [id]T) $ refl $ (cong mkCon∙ $ (cong (_ ▹_) $ [id]T)) $ refl $ id⁺ $ funext λ {Δ} → λ {refl → funextₕ (cong (Sub _) $ (cong (_ ▹_) $ [id]T)) λ {δ} {δ'} e →
    Σ-extₚ (cong (∘ₑ _) $ (cong (_ ▹_) $ [id]T) $ refl $ id⁺ $ e ∙ idl) (funext λ {δ₁} {δ₂} e1 → cong _≈_ $ (cong (∘ₑ _) $ (cong (_ ▹_) $ [id]T) $ refl $ id⁺ $ e) $ e1)}

  ⟨_⟩∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}(a∙ : Tm∙ Γ∙ A∙ a) → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ a ⟩
  ⟨_⟩∙ {A = A} {A∙} {a} a∙ = Sub∙.constructor (λ {Δ} γ →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    in coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺) ∘ ⟨ a[γ]t ⟩ ,ₚ ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh $ (cong (⟨⟩ₑ _) $ ≈A[γ]T $ ≈a[γ]t))
  
  ⟨⟩∘∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{a : Tm Γ A}{γ : Sub Δ Γ}
         {A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → ⟨ a∙ ⟩∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ ⟨⟩∘ ] _⁺∙ {A∙ = A∙} γ∙ ∘∙ ⟨ a∙ [ γ∙ ]t∙ ⟩∙
  ⟨⟩∘∙ {Γ} {Δ} {Γ∙} {Δ∙} {A} {a} {γ} {A∙} {a∙} {γ∙} = cong mkSub∙ $ ⟨⟩∘ $ funext λ {Θ} → λ {refl → funext λ {δ} → λ {refl →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,ₚ ≈A[γ∘δ]T) = ∣ A∙ ∣ γ∘δ
      (a[γ∘δ]t ,ₚ ≈a[γ∘δ]t) = ∣ a∙ ∣ γ∘δ
    in Σ-extₚ (cong ∘ₑ
                 $ refl
                 $ (cong (Θ ▹_) $ sym ≈A[γ∘δ]T)
                 $ refl
                 $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ)) $ refl $ coh)
                 $ (cong ⟨⟩ₑ $ refl $ sym ≈A[γ∘δ]T $ sym ≈a[γ∘δ]t)
              ∙ ass)

              (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ δ) $ ⟨⟩∘)})}}

  p∘⁺∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{γ : Sub Δ Γ}
         {A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → p∙ {A∙ = A∙} ∘∙ _⁺∙ {A∙ = A∙} γ∙  ~[ cong (Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) _) $ p∘⁺ ] γ∙ ∘∙ p∙ {A∙ = A∙ [ γ∙ ]T∙}
  p∘⁺∙ {Γ} {Δ} {Γ∙} {Δ∙} {A} {γ} {A∙} {γ∙} = cong mkSub∙ $ p∘⁺ $ funext λ {Θ} → λ {refl → funext λ {δ} → λ {refl →
    let
      (γ∘p∘δ ,ₚ ≈γ∘p∘δ) = ∣ γ∙ ∣ (p ∘ δ)
    in Σ-extₚ (sym ass ∙ cong (_∘ δ) $ p∘⁺ ∙ ass ∙ ≈γ∘p∘δ) (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ δ) $ p∘⁺)})}}
  
  p∘⟨⟩∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}
        → p∙ {A∙ = A∙} ∘∙ ⟨ a∙ ⟩∙ ~[ cong (Sub∙ _ _) $ p∘⟨⟩ ] id∙
  p∘⟨⟩∙ {Γ} {Γ∙} {A} {A∙} {a} {a∙} = cong mkSub∙ $ p∘⟨⟩ $ funext λ {Δ} → λ {refl → funext λ {γ} → λ {refl →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    in Σ-extₚ (sym ass
              ∙ cong ∘ₑ
                  $ refl
                  $ (cong (Δ ▹_) $ sym ≈A[γ]T)
                  $ refl
                  $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ p∘⁺)
                  $ (cong ⟨⟩ₑ $ refl $ sym ≈A[γ]T $ sym ≈a[γ]t)
              ∙ ass
              ∙ cong (γ ∘_) $ p∘⟨⟩
              ∙ idr)
              (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ γ) $ p∘⟨⟩)})}}

  ----------------- extra -----------------
  weave∙ : {A : Ty Γ}{γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ}
           {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{Ξ∙ : Con∙ Ξ}
           (A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Ξ∙ Γ∙ γ)(δ∙ : Sub∙ Θ∙ Ξ∙ δ)(γ'∙ : Sub∙ Δ∙ Γ∙ γ')(δ'∙ : Sub∙ Θ∙ Δ∙ δ')
           (e : γ ∘ δ ≈ γ' ∘ δ')(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] γ'∙ ∘∙ δ'∙)
         → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _) $ weave e ] A∙ [ γ'∙ ]T∙ [ δ'∙ ]T∙
  weave∙ A∙ γ∙ δ∙ γ'∙ δ'∙ e e∙ = sym ([∘]T∙ {A∙ = A∙} {γ∙} {δ∙}) ∙ cong ([]T∙ₑ _ _ _ _ _ A∙) $ e $ e∙ ∙ [∘]T∙ {A∙ = A∙} {γ'∙} {δ'∙}

  annihilate∙ : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ)(δ∙ : Sub∙ Γ∙ Δ∙ δ)
                (e : γ ∘ δ ≈ id)(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] id∙ {Γ∙ = Γ∙})
              → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _) $ annihilate e ] A∙
  annihilate∙ A∙ γ∙ δ∙ e e∙ = sym ([∘]T∙ {A∙ = A∙} {γ∙} {δ∙}) ∙ cong ([]T∙ₑ _ _ _ _ _ A∙) $ e $ e∙ ∙ [id]T∙

  [p][⁺]T∙ : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ)
           → A∙ [ p∙ {A∙ = A∙} ]T∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙ ~[ cong (Ty∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙)) $ [p][⁺]T ] A∙ [ γ∙ ]T∙ [ p∙ {A∙ = A∙ [ γ∙ ]T∙} ]T∙
  [p][⁺]T∙ A∙ γ∙ = weave∙ A∙ (p∙ {A∙ = A∙}) (_⁺∙ {A∙ = A∙} γ∙) γ∙ (p∙ {A∙ = A∙ [ γ∙ ]T∙}) p∘⁺ (p∘⁺∙ {A∙ = A∙} {γ∙})

  [p][⟨⟩]T∙ : {Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(a∙ : Tm∙ Γ∙ A∙ a)
            → A∙ [ p∙ {A∙ = A∙} ]T∙ [ ⟨ a∙ ⟩∙ ]T∙ ~[ cong (Ty∙ _) $ [p][⟨⟩]T ] A∙
  [p][⟨⟩]T∙ A∙ a∙ = annihilate∙ A∙ (p∙ {A∙ = A∙}) ⟨ a∙ ⟩∙ p∘⟨⟩ (p∘⟨⟩∙ {A∙ = A∙} {a∙ = a∙})
  -----------------------------------------
  []t∙ₑ = λ Γ Γ∙ A A∙ a Δ Δ∙ γ a∙ γ∙ → _[_]t∙ {Γ} {Γ∙} {A} {A∙} {a} {Δ} {Δ∙} {γ} a∙ γ∙

  ⟨⟩∙ₑ = λ Γ Γ∙ A A∙ a a∙ → ⟨_⟩∙ {Γ} {Γ∙} {A} {A∙} {a} a∙

  ∘∙ₑ = λ Γ Γ∙ Δ Δ∙ Θ Θ∙ γ δ γ∙ δ∙ → _∘∙_ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {Θ} {Θ∙} {δ} γ∙ δ∙

  ⁺∙ₑ = λ Γ Γ∙ Δ Δ∙ A A∙ γ γ∙  → _⁺∙ {Δ} {Γ} {Δ∙} {Γ∙} {A} {A∙} {γ} γ∙

  ▹∙ₑ = λ Γ Γ∙ A A∙ → _▹∙_ {Γ} {A} Γ∙ A∙

  p∙ₑ = λ Γ Γ∙ A A∙ → p∙ {Γ} {Γ∙} {A} {A∙}

  q∙ₑ = λ Γ Γ∙ A A∙ → q∙ {Γ} {Γ∙} {A} {A∙}

  q[⁺]∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{γ : Sub Δ Γ}{A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        → q∙ {A∙ = A∙} [ _⁺∙ {A∙ = A∙} γ∙ ]t∙ ~[ cong Tm∙ₑ $ cong (Δ ▹ A [ γ ]T) $ [p][⁺]T $ cong (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) $ [p][⁺]T∙ A∙ γ∙ $ q[⁺] ] q∙ {A∙ = A∙ [ γ∙ ]T∙}
  q[⁺]∙ {Γ} {Δ} {Γ∙} {Δ∙} {A} {γ} {A∙} {γ∙} = cong mkTm∙ₑ $ refl $ [p][⁺]T $ refl $ [p][⁺]T∙ A∙ γ∙ $ q[⁺] $ funext λ {Θ} → λ {refl → funext λ {δ} → λ {refl →
    Σ-extₚ ([∘]t ∙ cong ([]tₑ _ _) $ [p][⁺]T $ q[⁺] $ refl ∙ coh) (funextₕ (cong (Tm Θ) $ weave (sym ass ∙ cong (_∘ δ) $ p∘⁺ ∙ ass)) λ e → cong ~ₑ $ (cong (Tm Θ) $ (cong (_[ δ ]T) $ [p][⁺]T)) $ (cong []tₑ $ refl $ refl $ [p][⁺]T $ q[⁺] $ refl) $ (cong (Tm Θ) $ weave (sym ass ∙ cong (_∘ δ) $ p∘⁺ ∙ ass)) $ e)}}
      
  q[⟨⟩]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{a : Tm Γ A}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}
         → q∙ {A∙ = A∙} [ ⟨ a∙ ⟩∙ ]t∙ ~[ cong (λ x → Tm∙ₑ _ x Γ∙) $ [p][⟨⟩]T $ [p][⟨⟩]T∙ A∙ a∙ $ q[⟨⟩] ] a∙
  q[⟨⟩]∙ {Γ} {Γ∙} {A} {a} {A∙} {a∙} = cong mkTm∙ₑ $ refl $ [p][⟨⟩]T $ refl $ [p][⟨⟩]T∙ A∙ a∙ $ q[⟨⟩] $ funext λ {Δ} → λ {refl → funext λ {γ} → λ {refl →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    in Σ-extₚ
         ([∘]t ∙ cong []tₑ $ refl $ refl $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ [p][⁺]T ∙ cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ ≈A[γ]T $ (cong pₑ $ refl $ ≈A[γ]T)) $ (cong []tₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ refl $ sym coh ∙ q[⁺] ∙ cong qₑ $ refl $ ≈A[γ]T) $ refl ∙ q[⟨⟩])
         (funextₕ (cong (Tm Δ) $ (weave (sym ass ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ p∘⁺) $ (cong ⟨⟩ₑ $ refl $ sym ≈A[γ]T $ sym ≈a[γ]t) ∙ ass) ∙ [∘]T ∙ annihilate p∘⟨⟩ ∙ ≈A[γ]T)) λ e → cong ~ₑ $ (cong (Tm Δ) $ (cong _[ γ ]T $ annihilate p∘⟨⟩)) $ (cong []tₑ $ refl $ refl $ annihilate p∘⟨⟩ $ q[⟨⟩] $ refl) $ (cong (Tm Δ) $ (weave (sym ass ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ p∘⁺) $ (cong ⟨⟩ₑ $ refl $ sym ≈A[γ]T $ sym ≈a[γ]t) ∙ ass) ∙ [∘]T ∙ annihilate p∘⟨⟩ ∙ ≈A[γ]T)) $ e)}}

  ▹η∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
      → id∙ {Γ∙ = Γ∙ ▹∙ A∙} ~[ cong (Sub∙ _ _) $ ▹η ] _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ∘∙ ⟨ q∙ {A∙ = A∙} ⟩∙
  ▹η∙ {Γ} {Γ∙} {A} {A∙} = cong mkSub∙ $ ▹η $ funext λ {Δ} → λ {refl → funext λ {γ} → λ {refl →
    Σ-extₚ
      (sym idl ∙ cong (_∘ γ) $ ▹η ∙ ass ∙ cong ∘ₑ $ refl $ refl $ refl $ refl $ (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ sym [∘]T) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ sym [∘]T $ coh)))
      (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ γ) $ ▹η)})}}

  [▹η]T∙ : {Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B)
         → B∙ ~[ cong (Ty∙ _) $ [▹η]T ] B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙ [ ⟨ q∙ {A∙ = A∙} ⟩∙ ]T∙
  [▹η]T∙ A∙ B∙ = sym (annihilate∙ B∙ (_⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙})) ⟨ q∙ {A∙ = A∙} ⟩∙ (sym ▹η) (sym (▹η∙ {A∙ = A∙})))

  [⟨⟩][]T∙ : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B)(a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ)
           → B∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ [⟨⟩][]T ] B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙
  [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ = weave∙ B∙ ⟨ a∙ ⟩∙ γ∙ (_⁺∙ {A∙ = A∙} γ∙) ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ⟨⟩∘ (⟨⟩∘∙ {A∙ = A∙} {a∙} {γ∙})
------- ⊤ Σ stuff ---------------------------
{-
  ⊤∙   : Ty∙ Γ∙ ⊤
  ⊤[]∙ : ⊤∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊤[] ] ⊤∙
  tt∙  : Tm∙ Γ∙ ⊤∙ tt
  ⊤η∙  : a∙ ~[ cong Tm∙ₑ $ Γ ∎ $ refl $ Γ∙ ∎ $ refl $ ⊤η ] tt∙
  Σ∙   : (A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Σ A B)
  Σ[]∙ : Σ∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Σ[] ] Σ∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)
  _,∙_ : (a∙ : Tm∙ Γ∙ A∙ a)(b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b) → Tm∙ Γ∙ (Σ∙ A∙ B∙) (a , b)
  ,[]∙ : (a∙ ,∙ b∙) [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) $ Σ[] $ refl $ Σ[]∙ $ ,[] ] (a∙ [ γ∙ ]t∙ ,∙ coe (cong (Tm∙ₑ Δ) $ [⟨⟩][]T $ Δ∙ ∎ $ [⟨⟩][]T∙ $ coh) (b∙ [ γ∙ ]t∙))
  fst∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a → Tm∙ Γ∙ A∙ (fst a)
  snd∙ : (w∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a) → Tm∙ Γ∙ (B∙ [ ⟨ fst∙ w∙ ⟩∙ ]T∙) (snd a)
  Σβ₁∙ : fst∙ (a∙ ,∙ b∙) ~[ cong (Tm∙ _ _) $ Σβ₁ ] a∙
  Σβ₂∙ : {A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
       → snd∙ (a∙ ,∙ b∙)
           ~[ cong (Tm∙ₑ _) $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ refl $ (cong ([]T∙ₑ _ _ _ _ _ _) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ _) $ Σβ₁ $ Σβ₁∙)) $ Σβ₂ ]
         b∙
  Ση∙  : {w∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a} → w∙ ~[ cong (Tm∙ _ _ ) $ Ση ] (fst∙ w∙ ,∙ snd∙ w∙)

-- Π dolgok -------------------------------
  Π∙     : (A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Π A B)
  Π[]∙   : Π∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Π[] ] Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)
  lam∙   : (b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b) → Tm∙ Γ∙ (Π∙ A∙ B∙) (lam b)
  app∙   : (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(a∙ : Tm∙ Γ∙ A∙ a) → Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) (app f a)
  Πβ∙    : app∙ (lam∙ b∙) a∙ ~[ cong (Tm∙ _ _) $ Πβ ] b∙ [ ⟨ a∙ ⟩∙ ]t∙
  Πη∙    : lam∙ (app∙ (f∙ [ p∙ ]Π∙) q∙) ~[ cong (Tm∙ₑ _) $ (cong (Π _) $ sym [▹η]T) $ refl $ (cong (Π∙ₑ _ _ _ _) $ sym [▹η]T $ sym [▹η]T∙) $ Πη ] f∙
  lam[]∙ : lam∙ b∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ $ lam[] ] lam∙ (b∙ [ γ∙ ⁺∙ ]t∙)
  app[]∙ : app∙ f∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ $ app[] ] app∙ (f∙ [ γ∙ ]Π∙) (a∙ [ γ∙ ]t∙)

-- ⊥ dolgok ----------------------------
  ⊥∙         : Ty∙ Γ∙ ⊥
  ⊥[]∙       : {γ∙ : Sub∙ Δ∙ Γ∙ γ} → ⊥∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊥[] ] ⊥∙ {Γ∙ = Δ∙}
  exfalso∙   : (a∙ : Tm∙ Γ∙ ⊥∙ a) → Tm∙ {A = A} Γ∙ A∙ (exfalso a)
  exfalso[]∙ : exfalso∙ {A∙ = A∙} a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ _ _) $ exfalso[] ] exfalso∙ (coe (cong (Tm∙ₑ _) $ ⊥[] $ refl $ ⊥[]∙ $ coh) (a∙ [ γ∙ ]t∙))
-}
{-
D : DepModel {lzero} {lzero} {lzero}
D = DepModel.constructor
      (Sorts∙.constructor
        Con∙'
        Sub∙'
        Ty∙'
        Tm∙'
      )
      (CwF∙.constructor
        ∘∙'
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (Sigma∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (Pi∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (Empty∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (BoolT∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
-}
