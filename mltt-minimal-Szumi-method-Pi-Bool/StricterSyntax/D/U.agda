{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D.U {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

open import Lib
open import Syntax
open import D
open import InductionPrinciple D

import Sorts as D'
open D'.Con∙
open D'.Sub∙
open D'.Ty∙
open D'.Tm∙

private module T = DepModel.DepModel T

open import StricterSyntax.D.Sorts T
open import StricterSyntax.D.CwF T

IU∙ : UT∙ I ISorts∙ ICwF∙
IU∙ = record
       { U∙ = T.U∙
       ; El∙ = T.El∙
       ; cd∙ = T.cd∙
       ; Uβ∙ = T.Uβ∙
       ; Uη∙ = T.Uη∙
       ; U[]∙ = sym coh ∙ T.U[]∙
       ; cd[]∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙} →
                 let
                   (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                 in sym coh ∙ T.cd[]∙ ∙ cong T.cd∙ₑ $ refl $ refl $ refl $ sym un $ coh
       }
