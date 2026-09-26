{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module StricterSyntax.Sorts where

open import Lib
open import Syntax
open import DepModel
open I

private variable
  n m : ℕ
  Γ Δ Θ Ξ Ω : Con
  γ δ θ ξ : Sub Δ Γ
  A B C : Ty Γ n
  a b c d f : Tm Γ A

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

Sub∙∣∣ₑ = λ Δ Γ Δ∙ Γ∙ γ γ∙ Θ δ → Sub∙.∣_∣ {Δ} {Γ} {Δ∙} {Γ∙} {γ} γ∙ {Θ} δ

mkSub∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}(γ : Sub Δ Γ) → ((Θ : Con)(δ : Sub Θ Δ) → ∃[ θ ] γ ∘ δ ≈ θ) → Sub∙ Δ∙ Γ∙ γ
mkSub∙ _ f = Sub∙.constructor (λ {x} → f x)

mkSub∙ₑ : ∀ Δ Γ → (Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → ((Θ : Con)(δ : Sub Θ Δ) → ∃[ θ ] γ ∘ δ ≈ θ) → Sub∙ Δ∙ Γ∙ γ
mkSub∙ₑ _ _ _ _ _ f = Sub∙.constructor (λ {x} → f x)

record Ty∙ {Γ}(Γ∙ : Con∙ Γ)(n : ℕ)(A : Ty Γ n) : Set where
  field
    ∣_∣ : {Δ : Con}(γ : Sub Δ Γ) → ∃[ A[γ]T ] A [ γ ]T ≈ A[γ]T

  ∣_∣Tyₑ = λ Δ γ → ∣_∣ {Δ} γ

Ty∙ₑ = λ Γ Γ∙ n A → Ty∙ {Γ} Γ∙ n A

Ty∙∣∣ₑ = λ Γ Γ∙ n A A∙ Δ γ → Ty∙.∣_∣ {Γ} {Γ∙} {n} {A} A∙ {Δ} γ

mkTy∙ : ∀{Γ}{Γ∙ : Con∙ Γ}(A : Ty Γ n) → (∀ Δ → (γ : Sub Δ Γ) → ∃[ A[γ]T ] A [ γ ]T ≈ A[γ]T) → Ty∙ Γ∙ n A
mkTy∙ _ f = Ty∙.constructor (λ {x} → f x)

mkTy∙ₑ : ∀ Γ → (Γ∙ : Con∙ Γ)(A : Ty Γ n) → (∀ Δ → (γ : Sub Δ Γ) → ∃[ A[γ]T ] A [ γ ]T ≈ A[γ]T) → Ty∙ Γ∙ n A
mkTy∙ₑ _ _ A f = Ty∙.constructor (λ {x} → f x)

record Tm∙ {Γ}{A : Ty Γ n}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ n A)(a : Tm Γ A) : Set where
  field
    ∣_∣ : {Δ : Con}(γ : Sub Δ Γ) → let (A[γ]T ,-) = Ty∙.∣ A∙ ∣ γ in ∃[ a[γ]t ∶ Tm Δ A[γ]T ] a [ γ ]t ~[ cong (Tm _) $ un ] a[γ]t

  ∣_∣Tmₑ = λ Δ γ → ∣_∣ {Δ} γ

Tm∙ₑ = λ n Γ A Γ∙ A∙ a → Tm∙ {n} {Γ} {A} Γ∙ A∙ a

Tm∙∣∣ₑ = λ n Γ A Γ∙ A∙ a a∙ Δ γ → Tm∙.∣_∣ {n} {Γ} {A} {Γ∙} {A∙} {a} a∙ {Δ} γ

mkTm∙ : ∀{Γ}{n}{A : Ty Γ n}{Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ n A)(a : Tm Γ A) → (∀ Δ → (γ : Sub Δ Γ) → let (A[γ]T ,-) = Ty∙.∣ A∙ ∣ γ in ∃[ a[γ]t ∶ Tm Δ A[γ]T ] a [ γ ]t ~[ cong (Tm _) $ un ] a[γ]t) → Tm∙ Γ∙ A∙ a
mkTm∙ _ _ f = Tm∙.constructor (λ {x} → f x)

mkTm∙ₑ : ∀ Γ n → (A : Ty Γ n)(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ n A)(a : Tm Γ A) → (∀ Δ → (γ : Sub Δ Γ) → let (A[γ]T ,-) = Ty∙.∣ A∙ ∣ γ in ∃[ a[γ]t ∶ Tm Δ A[γ]T ] a [ γ ]t ~[ cong (Tm _) $ un ] a[γ]t) → Tm∙ Γ∙ A∙ a
mkTm∙ₑ _ _ _ _ _ _ f = Tm∙.constructor (λ {x} → f x)
