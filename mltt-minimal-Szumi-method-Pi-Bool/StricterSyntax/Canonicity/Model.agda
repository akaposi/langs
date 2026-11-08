{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module StricterSyntax.Canonicity.Model where

open import Lib
open import StricterSyntax.Syntax

private variable
  i j k : Level
  n : ℕ
  Γ Δ Θ Ξ : Con
  γ δ θ ξ : Sub Δ Γ
  A A₀ A₁ B : Ty i Γ
  a a₀ a₁ a₂ b t f Â : Tm Γ A
