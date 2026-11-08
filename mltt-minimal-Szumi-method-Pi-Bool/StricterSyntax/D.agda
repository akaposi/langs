{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

open import Syntax

open import StricterSyntax.D.Sorts T
open import StricterSyntax.D.CwF T
open import StricterSyntax.D.Lift T
open import StricterSyntax.D.U T
open import StricterSyntax.D.Pi T
open import StricterSyntax.D.Bool T

Dₛ : DepModel I {i} {j} {k}
Dₛ = record
      { sorts∙ = ISorts∙
      ; cwf∙ = ICwF∙
      ; liftT∙ = ILift∙
      ; uT∙ = IU∙
      ; pi∙ = IPi∙
      ; bool∙ = IBool∙
      }
