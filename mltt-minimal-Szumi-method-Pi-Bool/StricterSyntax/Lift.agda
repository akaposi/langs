{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

--------- Lift stuff -------------------------------
module StricterSyntax.Lift where

open import Lib
open import Syntax
open import DepModel
open I

open import StricterSyntax.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import StricterSyntax.CwF

Lift∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}(A∙ : Ty∙ Γ∙ n A) → Ty∙ Γ∙ (suc n) (Lift A)
Lift∙ A∙ = Ty∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
  in Lift A[γ]T ,ₚ Lift[] ∙ cong Lift $ un

lift∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{a}(a∙ : Tm∙ Γ∙ A∙ a) → Tm∙ Γ∙ (Lift∙ A∙) (lift a)
lift∙ {A∙} a∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
  in lift a[γ]t ,ₚ lift[] ∙ cong (liftₑ _ _) $ un $ un

unlift∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{a}(a∙ : Tm∙ Γ∙ (Lift∙ A∙) a) → Tm∙ Γ∙ A∙ (unlift a)
unlift∙ {A∙} a∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
  in unlift a[γ]t ,ₚ unlift[] ∙ cong (unliftₑ _ _) $ un $ (sym coh ∙ un)

lift∙ₑ = λ Γ Γ∙ n A A∙ a a∙ → lift∙ {Γ} {Γ∙} {n} {A} {A∙} {a} a∙
    
unlift∙ₑ = λ Γ Γ∙ n A A∙ a a∙ → unlift∙ {Γ} {Γ∙} {n} {A} {A∙} {a} a∙

Liftβ∙ : ∀{Γ n A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ n A}{a}{a∙ : Tm∙ Γ∙ A∙ a}
       → unlift∙ (lift∙ a∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ Liftβ ] a∙
Liftβ∙ {A∙} {a∙} = cong mkTm∙ $ refl $ Liftβ $ funext λ {Δ} → funext λ {γ} →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
  in Σ-extₚ Liftβ (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Liftβ) $ refl $ refl))

Liftη∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A a}{A∙ : Ty∙ Γ∙ n A}{a∙ : Tm∙ Γ∙ (Lift∙ A∙) a}
       → lift∙ (unlift∙ {A∙ = A∙} a∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ Liftη ] a∙
Liftη∙ {A∙} {a∙} = cong mkTm∙ $ refl $ Liftη $ funext λ {Δ} → funext λ {γ} →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
  in Σ-extₚ Liftη (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Liftη) $ refl $ refl))

Lift[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        → (Lift∙ A∙ [ γ∙ ]T∙) ~[ cong Ty∙ₑ $ refl $ refl $ refl $ Lift[] ] Lift∙ (A∙ [ γ∙ ]T∙)
Lift[]∙ = cong mkTy∙ $ Lift[] $ funext λ {Θ} → funext λ {δ} →
  Σ-extₚ refl (funext (cong ~ₑ $ refl $ (cong _[ δ ]T $ Lift[]) $ refl $ refl))

lift[]∙ : ∀{Γ n A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ n A}{a}{a∙ : Tm∙ Γ∙ A∙ a}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        → lift∙ a∙ [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ Lift[] $ refl $ Lift[]∙ {A∙ = A∙} {γ∙ = γ∙} $ lift[] ] lift∙ (a∙ [ γ∙ ]t∙)
lift[]∙ {A∙} {γ∙} = cong mkTm∙ₑ $ refl $ refl $ Lift[] $ refl $ Lift[]∙ {A∙ = A∙} {γ∙ = γ∙} $ lift[] $ funext λ {Θ} → funext λ {δ} →
  Σ-extₚ refl (funext (cong ~ₑ $ (cong (Tm Θ) $ (cong _[ δ ]T $ Lift[])) $ (cong []tₑ $ refl $ refl $ refl $ Lift[] $ lift[] $ refl) $ refl $ refl))

unlift[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A a}(A∙ : Ty∙ Γ∙ n A)(a∙ : Tm∙ Γ∙ (Lift∙ A∙) a){Δ}{Δ∙ : Con∙ Δ}{γ}(γ∙ : Sub∙ Δ∙ Γ∙ γ)
          → _[_]t∙ {A∙ = A∙} (unlift∙ a∙) γ∙ ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ unlift[] ] unlift∙ (coe (cong Tm∙ₑ $ refl $ refl $ Lift[] $ refl $ Lift[]∙ {A∙ = A∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
unlift[]∙ {Γ} {Γ∙} {n} {A} {a} A∙ a∙ {Δ} {Δ∙} {γ} γ∙ = sym Liftβ∙ ∙ cong unlift∙ₑ $ refl $ refl $ refl $ refl $ refl $ (sym lift[] ∙ cong _[ _ ]t $ Liftη ∙ coh) $ (sym (lift[]∙ {A∙ = A∙} {a∙ = unlift∙ a∙} {γ∙ = γ∙}) ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ Liftη $ refl $ refl $ refl $[ lift∙ {A∙ = A∙} (unlift∙ a∙) , a∙ ] Liftη∙ {A∙ = A∙} {a∙ = a∙} $ reflₑ γ∙ ∙ coh)
