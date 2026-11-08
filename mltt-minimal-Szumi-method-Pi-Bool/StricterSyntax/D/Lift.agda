{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D.Lift {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

open import Lib
open import Syntax

import Sorts as D'
open D'.Con∙
open D'.Sub∙
open D'.Ty∙
open D'.Tm∙

open import D
open import InductionPrinciple D

private module T = DepModel.DepModel T

open import StricterSyntax.D.Sorts T
open import StricterSyntax.D.CwF T

ILift∙ : LiftT∙ I ISorts∙ ICwF∙
ILift∙ = record
          { Lift∙ = T.Lift∙
          ; lift∙ = T.lift∙
          ; unlift∙ = T.unlift∙
          ; Liftβ∙ = T.Liftβ∙
          ; Liftη∙ = T.Liftη∙
          ; Lift[]∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙} →
                      let
                        (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                      in sym coh ∙ T.Lift[]∙ ∙ cong T.Lift∙ₑ $ refl $ refl $ refl $ sym un $ coh
          ; lift[]∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙} →
                      let
                        (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                        (a[γ]t ,-) = ∣ ⟦ a ⟧Tm ∣ γ
                      in sym coh ∙ T.lift[]∙ ∙ cong T.lift∙ₑ $ refl $ refl $ refl $ sym un $ coh $ sym un $ coh
          }
