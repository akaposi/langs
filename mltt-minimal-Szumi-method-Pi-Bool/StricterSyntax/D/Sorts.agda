{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D.Sorts {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

open import Lib
open import Syntax
open Iₛ

private module T = DepModel.DepModel T

Con∙ : Con → Set i
Con∙ = T.Con∙

Con∙ₑ = Con∙

Sub∙ : ∀{Δ Γ}(Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → Set j
Sub∙ = T.Sub∙

Sub∙ₑ : ∀ Δ Γ → (Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → Set j
Sub∙ₑ Δ Γ = Sub∙ {Δ} {Γ}

Ty∙ : ∀{Γ}(Γ∙ : Con∙ Γ)(n : ℕ)(A : Ty Γ n) → Set k
Ty∙ = T.Ty∙

Ty∙ₑ : ∀ Γ → (Γ∙ : Con∙ Γ)(n : ℕ)(A : Ty Γ n) → Set k
Ty∙ₑ Γ = Ty∙ {Γ}

Tm∙ : ∀{n Γ A}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ n A)(a : Tm Γ A) → Set j
Tm∙ = T.Tm∙

Tm∙ₑ : ∀ n Γ A → (Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ n A)(a : Tm Γ A) → Set j
Tm∙ₑ n Γ A = Tm∙ {n} {Γ} {A}

ISorts∙ : Sorts∙ I i j k j
ISorts∙ = record { Con∙ = Con∙ ; Sub∙ = Sub∙ ; Ty∙ = Ty∙ ; Tm∙ = Tm∙ }
