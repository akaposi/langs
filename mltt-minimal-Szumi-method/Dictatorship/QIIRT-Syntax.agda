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

module QIIRT where

  record Con∙ (Γ : Con) : Set where
    field
      instance ∣_∣ : L.⊤
  
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
  id∙ = mkSub∙ id λ _ δ → δ ,ₚ idl

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
  ε∙ = mkSub∙ ε λ Θ δ → ε ,ₚ ◇η

  ◇η∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{γ : Sub Γ ◇}{γ∙ : Sub∙ Γ∙ ◇∙ γ} → γ∙ ~[ cong (Sub∙ _ _) $ ◇η ] ε∙
  ◇η∙ {γ∙ = γ∙} = cong mkSub∙ $ ◇η $ funext λ {Θ} → λ {refl → funext λ {δ} → λ {refl →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    in Σ-extₚ ◇η (funext λ {z} → λ {refl → cong (_≈ z) $ (cong (_∘ δ) $ ◇η)})}}
  
  _[_]T∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{γ : Sub Δ Γ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Ty∙ Δ∙ (A [ γ ]T)
  _[_]T∙ {A = A} {γ} A∙ γ∙ = mkTy∙ (A [ γ ]T) λ Θ δ → 
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    in A [ γ∘δ ]T ,ₚ sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ

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
  _[_]t∙ {a = a} {γ} {A∙} a∙ γ∙ = mkTm∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t) λ Θ δ →
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
    in Σ-extₚ ≈a[γ]t (funextₕ (cong (Tm Δ) $ ≈A[γ]T) λ {z} e → cong ~ₑ $ (cong (Tm Δ) $ (cong _[ γ ]T $ [id]T)) $ (cong ([]tₑ _ _) $ [id]T $ [id]t $ refl) $ (cong (Tm Δ) $ {!!}) $ {!!})}}
  
  _▹∙_ : ∀{Γ}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A) → Con∙ (Γ ▹ A)
  _▹∙_ = {!!}
  
  p∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
  p∙ = {!!}
  
  q∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ {A∙ = A∙} ]T∙) q
  q∙ = {!!}
  
  _⁺∙ : ∀{Γ Δ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{γ : Sub Δ Γ}(γ∙ : Sub∙ Δ∙ Γ∙ γ)
      → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) (Γ∙ ▹∙ A∙) (γ ⁺)
  _⁺∙ = {!!}
  
  ∘⁺∙ : ∀{Γ Δ Θ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{A : Ty Γ}{γ : Sub Δ Γ}{δ : Sub Θ Δ}
        {A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}
      → (γ∙ ∘∙ δ∙) ⁺∙ ~[ cong Sub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Θ∙) $ [∘]T $ [∘]T∙ {A∙ = A∙} {γ∙} {δ∙}) $ cong (Γ∙ ▹∙ A∙) $ ∘⁺ ] γ∙ ⁺∙ ∘∙ δ∙ ⁺∙
  ∘⁺∙ = {!!}
  
{-
  id⁺∙    : id∙ ⁺∙ ~[ cong Sub∙ₑ $ (cong (Γ ▹_) $ [id]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Γ∙) $ [id]T $ [id]T∙) $ cong (Γ∙ ▹∙ A∙) $ id⁺ ] id∙
  
  ⟨_⟩∙    : (a∙ : Tm∙ Γ∙ A∙ a) → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ a ⟩
  
  ⟨⟩∘∙    : ⟨ a∙ ⟩∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ ⟨⟩∘ ] γ∙ ⁺∙ ∘∙ ⟨ a∙ [ γ∙ ]t∙ ⟩∙
  
  p∘⁺∙    : p∙ ∘∙ γ∙ ⁺∙ ~[ cong (Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) _) $ p∘⁺ ] γ∙ ∘∙ p∙
  
  p∘⟨⟩∙   : p∙ ∘∙ ⟨ a∙ ⟩∙ ~[ cong (Sub∙ _ _) $ p∘⟨⟩ ] id∙
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
