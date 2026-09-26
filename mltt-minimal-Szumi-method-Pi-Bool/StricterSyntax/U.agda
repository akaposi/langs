{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

--------- U stuff -------------------------------
module StricterSyntax.U where

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

U∙ : ∀{Γ}{Γ∙ : Con∙ Γ}(n : ℕ) → Ty∙ Γ∙ (suc n) (U n)
U∙ n = Ty∙.constructor λ _ → U n ,ₚ U[]

El∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n a}(a∙ : Tm∙ Γ∙ (U∙ n) a) → Ty∙ Γ∙ n (El a)
El∙ {a} a∙ = Ty∙.constructor λ γ →
  let
    (a[γ]t ,-) = ∣ a∙ ∣ γ
  in El a[γ]t ,ₚ El[] ∙ cong El $ (sym coh ∙ un)

cd∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}(A∙ : Ty∙ Γ∙ n A) → Tm∙ Γ∙ (U∙ n) (cd A)
cd∙ A∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
  in cd A[γ]T ,ₚ cd[] ∙ cong cd $ un

El∙ₑ = λ Γ Γ∙ n a a∙ → El∙ {Γ} {Γ∙} {n} {a} a∙

cd∙ₑ = λ Γ Γ∙ n A A∙ → cd∙ {Γ} {Γ∙} {n} {A} A∙

Uβ∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A} 
    → El∙ (cd∙ A∙) ~[ cong Ty∙ₑ $ refl $ refl $ refl $ Uβ ] A∙
Uβ∙ {A∙} = cong mkTy∙ $ Uβ $ funext λ {Δ} → funext λ {γ} →
  Σ-extₚ Uβ (funext (cong ~ₑ $ refl $ (cong _[ γ ]T $ Uβ) $ refl $ refl))

Uη∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n a}{a∙ : Tm∙ Γ∙ (U∙ n) a}
    → cd∙ (El∙ a∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ Uη ] a∙
Uη∙ {a∙} = cong mkTm∙ $ refl $ Uη $ funext λ {Δ} → funext λ {γ} →
  Σ-extₚ Uη (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Uη) $ refl $ refl))

U[]∙ : ∀{n Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → (U∙ n) [ γ∙ ]T∙ ~[ cong Ty∙ₑ $ refl $ refl $ refl $ U[] ] U∙ n
U[]∙ = cong mkTy∙ $ U[] $ funext λ {Δ} → funext λ {γ} →
  Σ-extₚ refl (funext (cong ~ₑ $ refl $ (cong _[ γ ]T $ U[]) $ refl $ refl))

cd[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
      → cd∙ A∙ [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ U[] $ refl $ U[]∙ {γ∙ = γ∙} $ cd[] ] cd∙ (A∙ [ γ∙ ]T∙)
cd[]∙ {γ∙} = cong mkTm∙ₑ $ refl $ refl $ U[] $ refl $ U[]∙ {γ∙ = γ∙} $ cd[] $ funext λ {Θ} → funext λ {δ} →
  Σ-extₚ refl (funext (cong ~ₑ $ (cong (Tm Θ) $ (cong _[ δ ]T $ U[])) $ (cong []tₑ $ refl $ refl $ refl $ U[] $ cd[] $ refl) $ refl $ refl))

El[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n a}(a∙ : Tm∙ Γ∙ (U∙ n) a){Δ}{Δ∙ : Con∙ Δ}{γ}(γ∙ : Sub∙ Δ∙ Γ∙ γ)
      → El∙ a∙ [ γ∙ ]T∙ ~[ cong Ty∙ₑ $ refl $ refl $ refl $ El[] ] El∙ (coe (cong Tm∙ₑ $ refl $ refl $ U[] $ refl $ U[]∙ {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
El[]∙ a∙ γ∙ = sym Uβ∙ ∙ cong El∙ₑ $ refl $ refl $ refl $ (sym cd[] ∙ cong _[ _ ]t $ Uη ∙ coh) $[ cd∙ (El∙ a∙ [ γ∙ ]T∙) , coe (cong Tm∙ₑ $ refl $ refl $ U[] $ refl $ U[]∙ {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙) ] (sym (cd[]∙ {A∙ = El∙ a∙} {γ∙ = γ∙}) ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ Uη $ refl $ refl $ refl $ Uη∙ {a∙ = a∙} $ reflₑ γ∙ ∙ coh)
