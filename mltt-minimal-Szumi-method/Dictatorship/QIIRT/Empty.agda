{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

----------- ⊥ stuff ----------------------------
module Dictatorship.QIIRT.Empty where

open import Lib
open import Dictatorship.Syntax
open import Dictatorship.DepModel
open I

open import Dictatorship.QIIRT.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import Dictatorship.QIIRT.CwF

⊥∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Ty∙ Γ∙ ⊥
⊥∙ = Ty∙.constructor λ _ → ⊥ ,- -- ⊥[]
  
⊥[]∙ : ∀{Δ}{Δ∙ : Con∙ Δ}{Γ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → ⊥∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊥[] ] ⊥∙ {Γ∙ = Δ∙}
⊥[]∙ {γ∙} = cong mkTy∙ $ ⊥[] $ funext λ {Θ} → funext λ {δ} → Σ-extₚ refl (funext (cong (_≈ _) $ (cong _[ δ ]T $ ⊥[])))
                                                                                                                
exfalso∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{a A}{A∙ : Ty∙ Γ∙ A}(a∙ : Tm∙ Γ∙ ⊥∙ a) → Tm∙ {A = A} Γ∙ A∙ (exfalso a)
exfalso∙ {A∙} a∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
  in exfalso a[γ]t ,ₚ exfalso[] ∙ cong exfalsoₑ $ refl $ un $ (sym coh ∙ un)
                                                                         
exfalso[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{a}{a∙ : Tm∙ Γ∙ ⊥∙ a}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
           → exfalso∙ {A∙ = A∙} a∙ [ γ∙ ]t∙
             ~[ cong (Tm∙ _ _) $ exfalso[] ]
             exfalso∙ (coe (cong (Tm∙ₑ _) $ ⊥[] $ refl $ ⊥[]∙ {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
exfalso[]∙ {A∙} {a} {a∙} {Δ} {γ∙} = cong mkTm∙ $ refl $ exfalso[] $ funext λ {Θ} → funext λ {δ} →
                let
                  (γ∘δ ,-) = ∣ γ∙ ∣ δ
                  (a[γ∘δ]t ,-) = ∣ a∙ ∣ γ∘δ
                  (a[γ][δ]t ,-) = ∣ coe (cong (Tm∙ₑ Δ) $ ⊥[] $ refl $ ⊥[]∙ {γ∙ = γ∙} $ coh {e = cong (Tm Δ) $ ⊥[]}) (a∙ [ γ∙ ]t∙) ∣ δ
                in Σ-extₚ (cong exfalso $ (sym un ∙ cong (a [_]t) $ sym un ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ ⊥[] $ coh $ refl ∙ un))
                          (funext (cong ~ₑ $ refl $ (cong []tₑ $ refl $ refl $ refl $ exfalso[] $ refl) $ refl $ refl))
