{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module Dictatorship.QIIRT.Syntax where

open import Lib
open import Dictatorship.Syntax
open import Dictatorship.Model
open import Dictatorship.DepModel

open import Dictatorship.QIIRT.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import Dictatorship.QIIRT.DepModel

module D = DepModel D

Sub↓ : ∀{Δ Γ}{Δ∙ : D.Con∙ Δ}{Γ∙ : D.Con∙ Γ}{γ : I.Sub Δ Γ} → D.Sub∙ Δ∙ Γ∙ γ → I.Sub Δ Γ
Sub↓ {γ = γ} _ = γ

Iₛ : Model {lzero} {lzero} {lzero}
Iₛ = record
      { sorts = record { Con = I.Con ; Sub = I.Sub ; Ty = I.Ty ; Tm = I.Tm }
      ; cwf = record
               { _∘_ = λ {Δ} {Γ} {Θ} γ δ → Sub↓ (D._∘∙_ {Δ} {_} {Γ} {_} {γ} {Θ} {_} {δ} ? ?)
               ; ass = {!!}
               ; id = {!!}
               ; idl = {!!}
               ; idr = {!!}
               ; ◇ = {!!}
               ; ε = {!!}
               ; ◇η = {!!}
               ; _[_]T = {!!}
               ; [∘]T = {!!}
               ; [id]T = {!!}
               ; _[_]t = {!!}
               ; [∘]t = {!!}
               ; [id]t = {!!}
               ; _▹_ = {!!}
               ; p = {!!}
               ; q = {!!}
               ; _⁺ = {!!}
               ; ∘⁺ = {!!}
               ; id⁺ = {!!}
               ; ⟨_⟩ = {!!}
               ; ⟨⟩∘ = {!!}
               ; p∘⁺ = {!!}
               ; p∘⟨⟩ = {!!}
               ; q[⁺] = {!!}
               ; q[⟨⟩] = {!!}
               ; ▹η = {!!}
               }
      ; sigma = {!!}
      ; pi = {!!}
      ; empty = {!!}
      ; bool = {!!}
      }

{-
D-ből és I-ből összerakni egy Iₛ-t (strict syntax, ahol az Iₛ-be az I-ből válogatjuk össze a dolgokat,
kivéve a helyettesítési szabályt, amit a D-ből szedünk össze.)
-}
