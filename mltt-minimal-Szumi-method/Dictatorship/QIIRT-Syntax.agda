{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module Dictatorship.QIIRT-Syntax where

open import Lib
open import Dictatorship.Syntax
open import Dictatorship.DepModel
open I

private variable
  Γ Δ Θ Ξ Ω : Con
  γ δ θ ξ : Sub Δ Γ
  A B C : Ty Γ
  a b c d f : Tm Γ A

module QIIRT-Sorts where

  record Con∙ (Γ : Con) : Set where
    field
      instance ∣_∣ : L.⊤

  mkCon∙ : ∀ Γ → Con∙ Γ
  mkCon∙ _ = _

  mkCon∙ₑ = mkCon∙

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

open QIIRT-Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

private variable
  Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ

module QIIRT-CwF where
  infixl 8 _∘∙_
  infixl 5 _▹∙_
  infixl 9 _[_]T∙ _[_]t∙
  infixl 10 _⁺∙
  infixl 11 ⟨_⟩∙

  _∘∙_ : {Δ : Con} {Δ∙ : Con∙ Δ} {Γ : Con} {Γ∙ : Con∙ Γ}
         {γ : Sub Δ Γ} {Θ : Con} {Θ∙ : Con∙ Θ} {δ : Sub Θ Δ} →
         Sub∙ Δ∙ Γ∙ γ → Sub∙ Θ∙ Δ∙ δ → Sub∙ Θ∙ Γ∙ (γ ∘ δ)
  _∘∙_ {γ} γ∙ δ∙ = Sub∙.constructor λ θ
                             → let (δ∘θ ,-) = ∣ δ∙ ∣ θ
                                   (γ∘δ∘θ ,-) = ∣ γ∙ ∣ δ∘θ
                               in γ∘δ∘θ ,ₚ ass ∙ cong (γ ∘_) $ un ∙ un

  ass∙ : {Δ Γ : Con} {Δ∙ : Con∙ Δ} {Γ∙ : Con∙ Γ}
         {γ : Sub Δ Γ} {γ∙ : Sub∙ Δ∙ Γ∙ γ} {Θ : Con}
         {Θ∙ : Con∙ Θ} {δ : Sub Θ Δ}
         {δ∙ : Sub∙ Θ∙ Δ∙ δ} {Ξ : Con} {Ξ∙ : Con∙ Ξ}
         {θ : Sub Ξ Θ} {θ∙ : Sub∙ Ξ∙ Θ∙ θ}
       → (γ∙ ∘∙ δ∙) ∘∙ θ∙ ~[ cong (Sub∙ _ _) $ ass ] γ∙ ∘∙ (δ∙ ∘∙ θ∙)
  ass∙ = 
    cong mkSub∙ $ ass $ funext (λ {Χ} → funext λ {χ} →
      Σ-extₚ refl (funext (cong (_≈ _) $ (cong (_∘ χ) $ ass))))

  id∙ : {Γ∙ : Con∙ Γ} → Sub∙ Γ∙ Γ∙ id
  id∙ = Sub∙.constructor λ δ → δ ,-

  idl∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → id∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ idl ] γ∙
  idl∙ {γ∙} = cong mkSub∙ $ idl $ funext λ {Θ} → funext λ {δ} →
    Σ-extₚ refl (funext (cong (_≈ _) $ (cong (_∘ δ) $ idl)))

  idr∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → γ∙ ∘∙ id∙ ~[ cong (Sub∙ _ _) $ idr ] γ∙
  idr∙ {γ∙} = cong mkSub∙ $ idr $ funext λ {Θ} → funext λ {δ} →
    Σ-extₚ refl (funext (cong (_≈ _) $ (cong (_∘ δ) $ idr)))

  ◇∙ : Con∙ ◇
  ◇∙ = _

  ε∙ : {Γ∙ : Con∙ Γ} → Sub∙ Γ∙ ◇∙ ε
  ε∙ = Sub∙.constructor λ δ → ε ,-

  ◇η∙ : {Γ∙ : Con∙ Γ}{γ : Sub Γ ◇}{γ∙ : Sub∙ Γ∙ ◇∙ γ} → γ∙ ~[ cong (Sub∙ _ _) $ ◇η ] ε∙
  ◇η∙ {γ∙} = cong mkSub∙ $ ◇η $ funext λ {Θ} → funext λ {δ} →
    Σ-extₚ ◇η (funext (cong (_≈ _) $ (cong (_∘ δ) $ ◇η)))
  
  _[_]T∙ : ∀{Γ∙ : Con∙ Γ}{A : Ty Γ}{Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Ty∙ Δ∙ (A [ γ ]T)
  _[_]T∙ {A} A∙ γ∙ = Ty∙.constructor λ {Θ} δ → 
    let
      (γ∘δ ,-) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
    in A[γ∘δ]T ,ₚ sym [∘]T ∙ cong (A [_]T) $ un {- ≈γ∘δ -} ∙ un -- ≈A[γ∘δ]T

  []T∙ₑ = λ Δ Γ A Δ∙ Γ∙ A∙ γ γ∙ → _[_]T∙ {Γ} {Γ∙} {A} {Δ} {Δ∙} {γ} A∙ γ∙

  [∘]T∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
          {Θ}{Θ∙ : Con∙ Θ}{δ : Sub Θ Δ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}
        → A∙ [ γ∙ ∘∙ δ∙ ]T∙ ~[ cong (Ty∙ _) $ [∘]T ] A∙ [ γ∙ ]T∙ [ δ∙ ]T∙
  [∘]T∙ = cong mkTy∙ $ [∘]T $ funext λ {Ξ} → funext λ {θ} →
    Σ-extₚ refl (funext (cong (_≈ _) $ (cong _[ θ ]T $ [∘]T)))

  [id]T∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
         → A∙ [ id∙ ]T∙ ~[ cong (Ty∙ _) $ [id]T ] A∙
  [id]T∙ {A∙} = cong mkTy∙ $ [id]T $ funext λ {Δ} → funext λ {γ} →
    Σ-extₚ refl (funext (cong (_≈ _) $ (cong (_[ γ ]T) $ [id]T)))

  _[_]t∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}
           {Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}(a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ)
         → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
  _[_]t∙ {a} a∙ γ∙ = Tm∙.constructor λ {Θ} δ →
    let
      (γ∘δ ,-) = ∣ γ∙ ∣ δ
      (a[γ∘δ]t ,-) = ∣ a∙ ∣ γ∘δ
    in a[γ∘δ]t ,ₚ sym [∘]t ∙ cong (a [_]t) $ un {- ≈γ∘δ -} ∙ un -- ≈a[γ∘δ]t

  [∘]t∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}{Δ}{Δ∙ : Con∙ Δ}
          {γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{Θ}{Θ∙ : Con∙ Θ}{δ : Sub Θ Δ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}
        → a∙ [ γ∙ ∘∙ δ∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Θ∙) $ [∘]T $ [∘]T∙ {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙} $ [∘]t ] a∙ [ γ∙ ]t∙ [ δ∙ ]t∙
  [∘]t∙ {A∙} {γ∙} {δ∙} = cong (mkTm∙ₑ _) $ [∘]T $ refl $ [∘]T∙ {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙} $ [∘]t $ funext λ {Ξ} → funext λ {θ} →
    Σ-extₚ refl (funext (cong ~ₑ $ (cong (Tm Ξ) $ (cong _[ θ ]T $ [∘]T)) $ (cong ([]tₑ _ _) $ [∘]T $ [∘]t $ refl) $ refl $ refl))
  
  [id]t∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}
         → a∙ [ id∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Γ∙) $ [id]T $ [id]T∙ $ [id]t ] a∙
  [id]t∙ = cong (mkTm∙ₑ _) $ [id]T $ refl $ [id]T∙ $ [id]t $ funext λ {Δ} → funext λ {γ} →
    Σ-extₚ refl (funext (cong ~ₑ $ (cong (Tm Δ) $ (cong _[ γ ]T $ [id]T)) $ (cong ([]tₑ _ _) $ [id]T $ [id]t $ refl) $ refl $ refl))
  
  _▹∙_ : ∀{Γ}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A) → Con∙ (Γ ▹ A)
  _▹∙_ _ _ = _
  
  p∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
  p∙ = Sub∙.constructor (λ {Δ} γ → p ∘ γ ,ₚ refl)
  
  q∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ {A∙ = A∙} ]T∙) q
  q∙ {A∙} = Tm∙.constructor λ {Δ} γ →
    let
      (_ ,-) = ∣ A∙ ∣ (p ∘ γ)
    in coe (cong (Tm _) $ (sym [∘]T ∙ un {- ≈A[p∘γ]T -})) (q [ γ ]t) ,ₚ coh
  
  _⁺∙ : ∀{Δ}{Δ∙ : Con∙ Δ}{Γ}{Γ∙ : Con∙ Γ}{γ : Sub Δ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}(γ∙ : Sub∙ Δ∙ Γ∙ γ)
      → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) (Γ∙ ▹∙ A∙) (γ ⁺)
  _⁺∙ {γ} _ = Sub∙.constructor λ {Θ} δ → γ ⁺ ∘ δ ,ₚ refl
  
  ∘⁺∙ : ∀{Δ}{Δ∙ : Con∙ Δ}{Γ}{γ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        {Θ}{δ : Sub Θ Δ}{Θ∙ : Con∙ Θ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
      → _⁺∙ {A∙ = A∙} (γ∙ ∘∙ δ∙) ~[ cong Sub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Θ∙) $ [∘]T $ [∘]T∙ {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙}) $ cong (Γ∙ ▹∙ A∙) $ ∘⁺ ] _⁺∙ {A∙ = A∙} γ∙ ∘∙ _⁺∙ {A∙ = A∙ [ γ∙ ]T∙} δ∙
  ∘⁺∙ {Θ} = cong mkSub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ refl $ (cong mkCon∙ $ (cong (Θ ▹_) $ [∘]T)) $ refl $ ∘⁺ $ funext λ {Ξ} → funextₕ (cong (Sub Ξ) $ (cong (Θ ▹_) $ [∘]T)) λ {θ} {θ'} e →
    Σ-extₚ (cong (∘ₑ _) $ (cong (Θ ▹_) $ [∘]T) $ refl $ ∘⁺ $ e ∙ ass) (funext (cong ~ₑ $ refl $ (cong (∘ₑ _) $ (cong (Θ ▹_) $ [∘]T) $ refl $ ∘⁺ $ e) $ refl $ refl))
  
  id⁺∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}
       → _⁺∙ {A∙ = A∙} id∙ ~[ cong Sub∙ₑ $ (cong (Γ ▹_) $ [id]T) $ cong (Γ ▹ A) $ (cong mkCon∙ $ (cong (Γ ▹_) $ [id]T)) $ cong (Γ∙ ▹∙ A∙) $ id⁺ ] id∙
  id⁺∙ = cong mkSub∙ₑ $ (cong (_ ▹_) $ [id]T) $ refl $ (cong mkCon∙ $ (cong (_ ▹_) $ [id]T)) $ refl $ id⁺ $ funext λ {Δ} → funextₕ (cong (Sub _) $ (cong (_ ▹_) $ [id]T)) λ {δ} {δ'} e →
    Σ-extₚ (cong (∘ₑ _) $ (cong (_ ▹_) $ [id]T) $ refl $ id⁺ $ e ∙ idl) (funext λ {z} → cong (_≈ z) $ (cong (∘ₑ _) $ (cong (_ ▹_) $ [id]T) $ refl $ id⁺ $ e))

  ⟨_⟩∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}(a∙ : Tm∙ Γ∙ A∙ a) → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ a ⟩
  ⟨_⟩∙ {A} {A∙} {a} a∙ = Sub∙.constructor (λ {Δ} γ →
    let
      (A[γ]T ,-) = ∣ A∙ ∣ γ
      (a[γ]t ,-) = ∣ a∙ ∣ γ
    in coe (cong Sub $ (cong (Δ ▹_) $ un {- ≈A[γ]T -}) $ refl) (γ ⁺) ∘ ⟨ a[γ]t ⟩ ,ₚ ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (Δ ▹_) $ un {- ≈A[γ]T -}) $ refl $ coh $ (cong (⟨⟩ₑ _) $ un {- ≈A[γ]T -} $ un {- ≈a[γ]t -}))
  
  ⟨⟩∘∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}
         {Δ}{Δ∙ : Con∙ Δ}{γ : Sub Δ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → ⟨ a∙ ⟩∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ ⟨⟩∘ ] _⁺∙ {A∙ = A∙} γ∙ ∘∙ ⟨ a∙ [ γ∙ ]t∙ ⟩∙
  ⟨⟩∘∙ {A} {A∙} {a∙} {γ∙} = cong mkSub∙ $ ⟨⟩∘ $ funext λ {Θ} → funext λ {δ} →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,ₚ ≈A[γ∘δ]T) = ∣ A∙ ∣ γ∘δ
      (a[γ∘δ]t ,ₚ ≈a[γ∘δ]t) = ∣ a∙ ∣ γ∘δ
    in Σ-extₚ (cong _∘_
                 $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)
                 $ (cong ⟨⟩ₑ $ refl $ (sym ≈A[γ∘δ]T ∙ ≈A[γ∘δ]T) $ (sym ≈a[γ∘δ]t ∙ ≈a[γ∘δ]t))
              ∙ ass)

              (funext λ {z} → cong (_≈ z) $ (cong (_∘ δ) $ ⟨⟩∘))

  p∘⁺∙ : ∀{Δ Γ}{Γ∙ : Con∙ Γ}{γ : Sub Δ Γ}{Δ∙ : Con∙ Δ}
         {γ∙ : Sub∙ Δ∙ Γ∙ γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
       → p∙ {A∙ = A∙} ∘∙ _⁺∙ {A∙ = A∙} γ∙  ~[ cong (Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) _) $ p∘⁺ ] γ∙ ∘∙ p∙ {A∙ = A∙ [ γ∙ ]T∙}
  p∘⁺∙ {γ∙} = cong mkSub∙ $ p∘⁺ $ funext λ {Θ} → funext λ {δ} →
    let
      (_ ,-) = ∣ γ∙ ∣ (p ∘ δ)
    in Σ-extₚ (sym ass ∙ cong (_∘ δ) $ p∘⁺ ∙ ass ∙ un) (funext λ {z} → cong (_≈ z) $ (cong (_∘ δ) $ p∘⁺))
  
  p∘⟨⟩∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}
        → p∙ {A∙ = A∙} ∘∙ ⟨ a∙ ⟩∙ ~[ cong (Sub∙ _ _) $ p∘⟨⟩ ] id∙
  p∘⟨⟩∙ {A∙} {a∙} = cong mkSub∙ $ p∘⟨⟩ $ funext λ {Δ} → funext λ {γ} →
    let
      (_ ,-) = ∣ A∙ ∣ γ
      (_ ,-) = ∣ a∙ ∣ γ
    in Σ-extₚ (sym ass
              ∙ cong ∘ₑ
                  $ refl
                  $ (cong (Δ ▹_) $ sym un)
                  $ refl
                  $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ p∘⁺)
                  $ (cong ⟨⟩ₑ $ refl $ sym un $ sym un)
              ∙ ass
              ∙ cong (γ ∘_) $ p∘⟨⟩
              ∙ idr)
              (funext λ {z} → cong (_≈ z) $ (cong (_∘ γ) $ p∘⟨⟩))

  ----------------- extra -----------------
  weave∙ : {A : Ty Γ}{γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ}
           {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{Θ∙ : Con∙ Θ}{Ξ∙ : Con∙ Ξ}
           (A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Ξ∙ Γ∙ γ)(δ∙ : Sub∙ Θ∙ Ξ∙ δ)(γ'∙ : Sub∙ Δ∙ Γ∙ γ')(δ'∙ : Sub∙ Θ∙ Δ∙ δ')
           (e : γ ∘ δ ≈ γ' ∘ δ')(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] γ'∙ ∘∙ δ'∙)
         → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _) $ weave e ] A∙ [ γ'∙ ]T∙ [ δ'∙ ]T∙
  weave∙ A∙ γ∙ δ∙ γ'∙ δ'∙ e e∙ = sym ([∘]T∙ {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙}) ∙ cong ([]T∙ₑ _ _ _ _ _ A∙) $ e $ e∙ ∙ [∘]T∙ {A∙ = A∙} {γ∙ = γ'∙} {δ∙ = δ'∙}

  annihilate∙ : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ)(δ∙ : Sub∙ Γ∙ Δ∙ δ)
                (e : γ ∘ δ ≈ id)(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] id∙ {Γ∙ = Γ∙})
              → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _) $ annihilate e ] A∙
  annihilate∙ A∙ γ∙ δ∙ e e∙ = sym ([∘]T∙ {A∙ = A∙} {γ∙ = γ∙} {δ∙ = δ∙}) ∙ cong ([]T∙ₑ _ _ _ _ _ A∙) $ e $ e∙ ∙ [id]T∙

  [p][⁺]T∙ : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ)
           → A∙ [ p∙ {A∙ = A∙} ]T∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙ ~[ cong (Ty∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙)) $ [p][⁺]T ] A∙ [ γ∙ ]T∙ [ p∙ {A∙ = A∙ [ γ∙ ]T∙} ]T∙
  [p][⁺]T∙ A∙ γ∙ = weave∙ A∙ (p∙ {A∙ = A∙}) (_⁺∙ {A∙ = A∙} γ∙) γ∙ (p∙ {A∙ = A∙ [ γ∙ ]T∙}) p∘⁺ (p∘⁺∙ {γ∙ = γ∙} {A∙ = A∙})

  [p][⟨⟩]T∙ : {Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(a∙ : Tm∙ Γ∙ A∙ a)
            → A∙ [ p∙ {A∙ = A∙} ]T∙ [ ⟨ a∙ ⟩∙ ]T∙ ~[ cong (Ty∙ _) $ [p][⟨⟩]T ] A∙
  [p][⟨⟩]T∙ A∙ a∙ = annihilate∙ A∙ (p∙ {A∙ = A∙}) ⟨ a∙ ⟩∙ p∘⟨⟩ (p∘⟨⟩∙ {A∙ = A∙} {a∙ = a∙})
  -----------------------------------------
  []t∙ₑ = λ Γ Γ∙ A A∙ a Δ Δ∙ γ a∙ γ∙ → _[_]t∙ {Γ} {Γ∙} {A} {A∙} {a} {Δ} {Δ∙} {γ} a∙ γ∙

  ⟨⟩∙ₑ = λ Γ Γ∙ A A∙ a a∙ → ⟨_⟩∙ {Γ} {Γ∙} {A} {A∙} {a} a∙

  ∘∙ₑ = λ Γ Γ∙ Δ Δ∙ Θ Θ∙ γ δ γ∙ δ∙ → _∘∙_ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {Θ} {Θ∙} {δ} γ∙ δ∙

  ⁺∙ₑ = λ Γ Γ∙ Δ Δ∙ A A∙ γ γ∙  → _⁺∙ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {A} {A∙} γ∙

  ▹∙ₑ = λ Γ Γ∙ A A∙ → _▹∙_ {Γ} {A} Γ∙ A∙

  p∙ₑ = λ Γ Γ∙ A A∙ → p∙ {Γ} {Γ∙} {A} {A∙}

  q∙ₑ = λ Γ Γ∙ A A∙ → q∙ {Γ} {Γ∙} {A} {A∙}

  q[⁺]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{Δ}{γ : Sub Δ Γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
        → q∙ {A∙ = A∙} [ _⁺∙ {A∙ = A∙} γ∙ ]t∙ ~[ cong Tm∙ₑ $ cong (Δ ▹ A [ γ ]T) $ [p][⁺]T $ cong (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) $ [p][⁺]T∙ A∙ γ∙ $ q[⁺] ] q∙ {A∙ = A∙ [ γ∙ ]T∙}
  q[⁺]∙ {γ∙} {A∙} = cong mkTm∙ₑ $ refl $ [p][⁺]T $ refl $ [p][⁺]T∙ A∙ γ∙ $ q[⁺] $ funext λ {Θ} → funext λ {δ} →
    let
      (γ∘[p∘δ] ,ₚ ≈γ∘[p∘δ]) = ∣ γ∙ ∣ (p ∘ δ)
      (A[γ∘[p∘δ]]T ,ₚ ≈A[γ∘[p∘δ]]T) = ∣ A∙ ∣ γ∘[p∘δ]
    in Σ-extₚ (sym coh ∙ [∘]t ∙ cong ([]tₑ _ _) $ [p][⁺]T $ q[⁺] $ refl ∙ coh) (funextₕ (cong (Tm Θ) $ (cong (λ x → L.fst (∣ A∙ ∣ x)) $ (sym ass ∙ cong (_∘ δ) $ p∘⁺ ∙ ass ∙ ≈γ∘[p∘δ]))) λ e → cong ~ₑ $ (cong (Tm Θ) $ (cong (_[ δ ]T) $ [p][⁺]T)) $ (cong []tₑ $ refl $ refl $ [p][⁺]T $ q[⁺] $ refl) $ (cong (Tm Θ) $ (cong (λ x → L.fst (∣ A∙ ∣ x)) $ (sym ass ∙ cong (_∘ δ) $ p∘⁺ ∙ ass ∙ ≈γ∘[p∘δ]))) $ e)

  q[⟨⟩]∙ : ∀{Γ}{A : Ty Γ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a : Tm Γ A}{a∙ : Tm∙ Γ∙ A∙ a}
         → q∙ {A∙ = A∙} [ ⟨ a∙ ⟩∙ ]t∙ ~[ cong (λ x → Tm∙ₑ _ x Γ∙) $ [p][⟨⟩]T $ [p][⟨⟩]T∙ A∙ a∙ $ q[⟨⟩] ] a∙
  q[⟨⟩]∙ {A∙} {a∙} = cong mkTm∙ₑ $ refl $ [p][⟨⟩]T $ refl $ [p][⟨⟩]T∙ A∙ a∙ $ q[⟨⟩] $ funext λ {Δ} → funext λ {γ} →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    in Σ-extₚ
         (sym coh ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ [p][⁺]T ∙ cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ ≈A[γ]T $ (cong pₑ $ refl $ ≈A[γ]T)) $ (cong []tₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ refl $ sym coh ∙ q[⁺] ∙ cong qₑ $ refl $ ≈A[γ]T) $ refl ∙ q[⟨⟩])
         (funextₕ (cong (Tm Δ) $ (cong (λ x y → L.fst (∣ A∙ ∣ {x} y)) $ refl $ (sym ass ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ p∘⁺) $ (cong ⟨⟩ₑ $ refl $ sym ≈A[γ]T $ sym ≈a[γ]t) ∙ ass ∙ cong (γ ∘_) $ p∘⟨⟩ ∙ idr)))
            λ e → cong ~ₑ $ (cong (Tm Δ) $ (cong _[ γ ]T $ annihilate p∘⟨⟩)) $ (cong []tₑ $ refl $ refl $ annihilate p∘⟨⟩ $ q[⟨⟩] $ refl) $ (cong (Tm Δ) $ (cong (λ x y → L.fst (∣ A∙ ∣ {x} y)) $ refl $ (sym ass ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym ≈A[γ]T) $ refl $ sym coh ∙ p∘⁺) $ (cong ⟨⟩ₑ $ refl $ sym ≈A[γ]T $ sym ≈a[γ]t) ∙ ass ∙ cong (γ ∘_) $ p∘⟨⟩ ∙ idr))) $ e)

  ▹η∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A : Ty Γ}{A∙ : Ty∙ Γ∙ A}
      → id∙ {Γ∙ = Γ∙ ▹∙ A∙} ~[ cong (Sub∙ _ _) $ ▹η ] _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ∘∙ ⟨ q∙ {A∙ = A∙} ⟩∙
  ▹η∙ {A∙} = cong mkSub∙ $ ▹η $ funext λ {Δ} → funext λ {γ} →
    let
      (A[p∘γ]T ,ₚ ≈A[p∘γ]T) = ∣ A∙ ∣ (p ∘ γ)
    in Σ-extₚ
      (sym idl ∙ cong (_∘ γ) $ ▹η ∙ ass ∙ cong ∘ₑ $ refl $ refl $ refl $ refl $ (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ (sym [∘]T ∙ ≈A[p∘γ]T)) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ (sym [∘]T ∙ ≈A[p∘γ]T) $ coh)))
      (funext λ {z} → cong (_≈ z) $ (cong (_∘ γ) $ ▹η))

  [▹η]T∙ : {Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B)
         → B∙ ~[ cong (Ty∙ _) $ [▹η]T ] B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙ [ ⟨ q∙ {A∙ = A∙} ⟩∙ ]T∙
  [▹η]T∙ A∙ B∙ = sym (annihilate∙ B∙ (_⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙})) ⟨ q∙ {A∙ = A∙} ⟩∙ (sym ▹η) (sym (▹η∙ {A∙ = A∙})))

  [⟨⟩][]T∙ : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B)(a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ)
           → B∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ [⟨⟩][]T ] B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙
  [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ = weave∙ B∙ ⟨ a∙ ⟩∙ γ∙ (_⁺∙ {A∙ = A∙} γ∙) ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ⟨⟩∘ (⟨⟩∘∙ {A∙ = A∙} {a∙ = a∙} {γ∙ = γ∙})

open QIIRT-CwF

------- ⊤ Σ stuff ---------------------------
module QIIRT-Sigma where
  infixr 5 _,∙_

  ⊤∙ : {Γ∙ : Con∙ Γ} → Ty∙ Γ∙ ⊤
  ⊤∙ = Ty∙.constructor (λ _ → ⊤ ,ₚ ⊤[])
  
  ⊤[]∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → ⊤∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊤[] ] ⊤∙
  ⊤[]∙ {γ∙} = cong mkTy∙ $ ⊤[] $ funext λ {Θ} → funext λ {δ} →
    Σ-extₚ refl (funext λ {z} → cong (_≈ z) $ (cong _[ δ ]T $ ⊤[]))
  
  tt∙ : {Γ∙ : Con∙ Γ} → Tm∙ Γ∙ ⊤∙ tt
  tt∙ = Tm∙.constructor (λ _ → tt ,ₚ tt[])

  ⊤η∙ : ∀{Γ a}{Γ∙ : Con∙ Γ}{a∙ : Tm∙ Γ∙ ⊤∙ a}
      → a∙ ~[ cong Tm∙ₑ $ Γ ∎ $ refl $ Γ∙ ∎ $ refl $ ⊤η ] tt∙
  ⊤η∙ = cong mkTm∙ $ refl $ ⊤η $ funext λ {Δ} → funext λ {γ} →
    Σ-extₚ ⊤η (funext λ {z} → cong ~ₑ $ refl $ (cong _[ γ ]t $ ⊤η) $ refl $ refl)

  Σ∙ : ∀{Γ∙ : Con∙ Γ}{A B}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Σ A B)
  Σ∙ {B} A∙ B∙ = mkTy∙ _ λ Δ γ →
    let
      (A[γ]T ,-) = ∣ A∙ ∣ γ
      γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ un) $ refl) (γ ⁺)
      (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
    in Σ A[γ]T B[γ⁺]T ,ₚ Σ[] ∙ cong Σ $ un $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ un) $ refl $ coh ∙ un)

  Σ[]∙ : ∀{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → Σ∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Σ[] ] Σ∙ (A∙ [ γ∙ ]T∙) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)
  Σ[]∙ {A} {A∙} {B∙} {γ∙} = cong mkTy∙ $ Σ[] $ funext λ {Θ} → funext λ {δ} →
    let
      (γ∘δ ,-) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
    in Σ-extₚ
         (cong (Σ _) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh)))
         (funext λ {z} → cong (_≈ z) $ (cong _[ δ ]T $ Σ[]))

  _,∙_ : ∀{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{a B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b}
         (a∙ : Tm∙ Γ∙ A∙ a)(b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b)
       → Tm∙ Γ∙ (Σ∙ A∙ B∙) (a , b)
  _,∙_ {A∙} {B} {B∙} a∙ b∙ = Tm∙.constructor (λ {Δ} γ →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
      (B[γ⁺]T ,ₚ ≈B[γ⁺]T) = ∣ B∙ ∣ γ⁺
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
      (B[γ⁺∘⟨a[γ]t⟩]T ,ₚ ≈B[γ⁺∘⟨a[γ]t⟩]T) = ∣ B∙ ∣ (γ⁺ ∘ ⟨ a[γ]t ⟩)
      (b[γ]t ,ₚ ≈b[γ]t) = ∣ b∙ ∣ γ
    in a[γ]t , coe (cong (Tm Δ) $ (sym ≈B[γ⁺∘⟨a[γ]t⟩]T ∙ [∘]T ∙ cong (_[ ⟨ a[γ]t ⟩ ]T) $ ≈B[γ⁺]T)) b[γ]t ,ₚ ,[] ∙ cong ,ₑ $ refl $ ≈A[γ]T $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh ∙ ≈B[γ⁺]T) $ ≈a[γ]t $ (sym coh ∙ ≈b[γ]t ∙ coh))
  
  ,[]∙ : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a}{a∙ : Tm∙ Γ∙ A∙ a}{B b}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}
         {b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}{Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → (_,∙_ {B∙ = B∙} a∙ b∙) [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ ,[] ] (_,∙_ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (a∙ [ γ∙ ]t∙) (coe (cong Tm∙ₑ $ refl $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ $ coh) (b∙ [ γ∙ ]t∙)))
  ,[]∙ {A} {A∙} {a∙} {b} {B∙} {b∙} {Δ} {γ} {γ∙} = cong mkTm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ ,[] $ funext λ {Θ} → funext λ {δ} →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,ₚ ≈A[γ∘δ]T) = ∣ A∙ ∣ γ∘δ
      γ∘δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ ≈A[γ∘δ]T) $ refl) (γ∘δ ⁺)
      (b[γ∘δ]t ,ₚ ≈b[γ∘δ]t) = ∣ b∙ ∣ γ∘δ
      (b[γ][δ]t ,ₚ ≈b[γ][δ]t) = ∣ coe (cong Tm∙ₑ $ refl $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ $ coh {e = cong (Tm Δ) $ [⟨⟩][]T}) (b∙ [ γ∙ ]t∙) ∣ δ
    in Σ-extₚ
         (cong ,ₑ $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)) $ refl $ (sym coh ∙ sym ≈b[γ∘δ]t ∙ cong (b [_]t) $ sym ≈γ∘δ ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ [⟨⟩][]T $ coh $ refl ∙ ≈b[γ][δ]t ∙ coh))
         (funextₕ (cong (Tm Θ) $ (cong Σ $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh))))
                  λ e → cong ~ₑ $ (cong (Tm Θ) $ (cong _[ δ ]T $ Σ[])) $ (cong []tₑ $ refl $ refl $ Σ[] $ ,[] $ refl) $ (cong (Tm Θ) $ (cong Σ $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)))) $ e)

  fst∙ : ∀{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a} → Tm∙ Γ∙ (Σ∙ A∙ B∙) a → Tm∙ Γ∙ A∙ (fst a)
  fst∙ {A∙ = A∙} {B∙} a∙ = Tm∙.constructor λ {Δ} γ →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
      γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
      (B[γ⁺]T ,ₚ ≈B[γ⁺]T) = ∣ B∙ ∣ γ⁺
    in fst a[γ]t ,ₚ fst[] ∙ cong fstₑ $ refl $ ≈A[γ]T $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh ∙ ≈B[γ⁺]T) $ (sym coh ∙ ≈a[γ]t)

  snd∙ : ∀{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a}(a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a) → Tm∙ Γ∙ (B∙ [ ⟨ fst∙ {A∙ = A∙} {B∙ = B∙} a∙ ⟩∙ ]T∙) (snd a)
  snd∙ {A∙} {B∙} a∙ = Tm∙.constructor λ {Δ} γ →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
      γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
      (B[γ⁺]T ,ₚ ≈B[γ⁺]T) = ∣ B∙ ∣ γ⁺
      (B[γ⁺∘⟨⟩]T ,ₚ ≈B[γ⁺∘⟨⟩]T) = ∣ B∙ ∣ (γ⁺ ∘ ⟨ fst a[γ]t ⟩)
    in coe (cong (Tm Δ) $ (cong _[ ⟨ fst a[γ]t ⟩ ]T $ sym ≈B[γ⁺]T ∙ sym [∘]T ∙ ≈B[γ⁺∘⟨⟩]T)) (snd a[γ]t)
    ,ₚ snd[] ∙ cong sndₑ $ refl $ ≈A[γ]T $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh ∙ ≈B[γ⁺]T) $ (sym coh ∙ ≈a[γ]t) ∙ coh

  Σβ₁∙ : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a}{a∙ : Tm∙ Γ∙ A∙ a}{B b}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
       → fst∙ {B∙ = B∙} (_,∙_ {B∙ = B∙} a∙ b∙) ~[ cong (Tm∙ _ _) $ Σβ₁ ] a∙
  Σβ₁∙ {A∙} {a∙} = cong mkTm∙ $ refl $ Σβ₁ $ funext λ {Δ} → funext λ {γ} →
    Σ-extₚ Σβ₁ (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Σβ₁) $ refl $ refl))

  Σβ₂∙ : ∀{Γ∙ : Con∙ Γ}{A a B b}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
       → snd∙ {A∙ = A∙} {B∙ = B∙} (_,∙_ {B∙ = B∙} a∙ b∙)
           ~[ cong (Tm∙ₑ _) $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ refl $ (cong ([]T∙ₑ Γ (Γ ▹ A) B Γ∙ (Γ∙ ▹∙ A∙) B∙) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ A∙) $ Σβ₁ $ Σβ₁∙ {a∙ = a∙} {B∙ = B∙} {b∙ = b∙})) $ Σβ₂ ]
         b∙
  Σβ₂∙ {Γ} {Γ∙} {A} {a} {B} {b} {A∙} {a∙} {B∙} {b∙} = cong mkTm∙ₑ
    $ refl
    $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁)
    $ refl
    $ (cong ([]T∙ₑ Γ (Γ ▹ A) B Γ∙ (Γ∙ ▹∙ A∙) B∙) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ A∙) $ Σβ₁ $ Σβ₁∙ {a∙ = a∙} {B∙ = B∙} {b∙ = b∙}))
    $ Σβ₂
    $ funext λ {Δ} → funext λ {γ} →
      let
        (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
        γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
      in Σ-extₚ
           (sym coh ∙ Σβ₂ ∙ sym coh)
           (funextₕ (cong (Tm Δ) $ (cong (λ y → L.fst (∣ B∙ ∣ (γ⁺ ∘ ⟨ y ⟩))) $ Σβ₁))
                    λ e → cong ~ₑ $ (cong (λ x → Tm Δ (B [ ⟨ x ⟩ ]T [ γ ]T)) $ Σβ₁) $ (cong []tₑ $ refl $ refl $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ Σβ₂ $ refl) $ (cong (Tm Δ) $ (cong (λ y → L.fst (∣ B∙ ∣ (coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺) ∘ ⟨ y ⟩))) $ Σβ₁)) $ e)

  Ση∙ : ∀{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a}{a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a}
      → a∙ ~[ cong (Tm∙ _ _ ) $ Ση ] (_,∙_ {A∙ = A∙} {B∙ = B∙} (fst∙ {B∙ = B∙} a∙) (snd∙ {A∙ = A∙} {B∙ = B∙} a∙))
  Ση∙ = cong mkTm∙ $ refl $ Ση $ funext λ {Δ} → funext λ {γ} →
    Σ-extₚ (Ση ∙ cong _,_ $ refl $ (coh ∙ coh)) (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Ση) $ refl $ refl))

  -------- ⊤ Σ extra stuff --------

  tt[]∙ : ∀{Γ∙ : Con∙ Γ}{Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        → tt∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) $ ⊤[] $ Δ∙ ∎ $ ⊤[]∙ {γ∙ = γ∙} $ tt[] ] tt∙
  tt[]∙ {γ∙ = γ∙} = coh ∙ ⊤η∙ {a∙ = coe (cong Tm∙ₑ $ refl $ ⊤[] $ refl $ ⊤[]∙ {γ∙ = γ∙} $ tt[]) (tt∙ [ γ∙ ]t∙)}

  fst∙ₑ = λ Γ Γ∙ A A∙ B B∙ a a∙ → fst∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {a} a∙
  
  fst[]∙ : ∀{Γ∙ : Con∙ Γ}{A B a}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
         → fst∙ {A∙ = A∙} {B∙ = B∙} a∙ [ γ∙ ]t∙
             ~[ cong (Tm∙ _ _) $ fst[] ]
           fst∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (coe (cong Tm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
  fst[]∙ {A} {A∙} {B∙} {a∙} {γ∙} = cong mkTm∙ $ refl $ fst[] $ funext λ {Θ} → funext λ {δ} →
    let
      (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,ₚ ≈A[γ∘δ]T) = ∣ A∙ ∣ γ∘δ
      (a[γ∘δ]t ,ₚ ≈a[γ∘δ]t) = ∣ a∙ ∣ γ∘δ
      (a[γ][δ]t ,ₚ ≈a[γ][δ]t) = ∣ coe (cong Tm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙) ∣ δ
    in Σ-extₚ
         (cong fstₑ $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)) $ (sym ≈a[γ∘δ]t ∙ cong []tₑ $ refl $ refl $ refl $ refl $ sym ≈γ∘δ ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ Σ[] $ coh $ refl ∙ ≈a[γ][δ]t))
         (funext (cong ~ₑ $ refl $ (cong []tₑ $ refl $ refl $ refl $ fst[] $ refl) $ refl $ refl))

  snd∙ₑ = λ Γ Γ∙ A A∙ B B∙ b b∙ → snd∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {b} b∙

  snd[]∙ : ∀{Γ∙ : Con∙ Γ}{A B a}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a}
           {Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
         → snd∙ {A∙ = A∙} {B∙ = B∙} a∙ [ γ∙ ]t∙
             ~[ cong (Tm∙ₑ _) $ ([⟨⟩][]T ∙ cong (λ x → B [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) $ refl $ ([⟨⟩][]T∙ A∙ B∙ (fst∙ {B∙ = B∙} a∙) γ∙ ∙ cong ([]T∙ₑ _ _ _ _ _ (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)) $ (cong ⟨_⟩ $ fst[]) $ (cong (⟨⟩∙ₑ _ _ _ _) $ fst[] $ fst[]∙ {A∙ = A∙} {B∙ = B∙} {a∙ = a∙} {γ∙ = γ∙} )) $ snd[] ]
           snd∙ {A∙ = A∙ [ γ∙ ]T∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (coe (cong Tm∙ₑ $ Δ ∎ $ Σ[] $ Δ∙ ∎ $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
  snd[]∙ {A} {B} {A∙} {B∙} {a∙} {γ} {γ∙} =
    cong mkTm∙ₑ
      $ refl
      $ ([⟨⟩][]T ∙ cong (λ x → B [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[])
      $ refl
      $ (cong mkTy∙ₑ $ refl $ refl $ ([⟨⟩][]T ∙ cong (λ x → B [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) $ funext λ {Θ} → funext λ {δ} →
          let
            (γ∘δ ,-) = ∣ γ∙ ∣ δ
            (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
            (a[γ∘δ]t ,-) = ∣ a∙ ∣ γ∘δ
          in Σ-extₚ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (cong ∘ₑ $ refl $ (cong (Θ ▹_) $ (sym un ∙ cong (A [_]T) $ sym un)) $ refl $ {!!} $ {!!} ∙ {!!})) {!!})
      $ snd[]
      $ funext λ {Θ} → funext λ {δ} → {!!}
    -- sym (cong (snd∙ₑ Δ Δ∙ (A [ γ ]T) (A∙ [ γ∙ ]T∙) (B [ γ ⁺ ]T) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)) $ {!!} $ (sym coh ∙ {!!}) ∙ Σβ₂∙ {A∙ = A∙ [ γ∙ ]T∙} {a∙ = []t∙ₑ _ _ _ A∙ _ _ _ _ (fst∙ {B∙ = B∙} a∙) γ∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} ∙ sym coh)
    -- sym (cong (snd∙ₑ _ _ _ _ _ _) $ (sym coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) $ (sym coh ∙ cong ([]t∙ₑ _ _ _ _) $ Ση $ refl $ refl $ refl $ Ση∙ $ refl ∙ ,[]∙) ∙ Σβ₂∙ ∙ sym coh)

{-
--------- Π dolgok -------------------------------
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
-- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -} -- -}
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
