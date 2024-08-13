{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients

open import untyped-sk.Model

module untyped-sk.AModel where

infixl 5 _·_
infix  4 _↦_ _↦*_

data RTm : Set where
  S K : RTm
  _·_ : RTm → RTm → RTm

data _↦_ : RTm → RTm → Set where
  idR   : {u : RTm} → u ↦ u
  KβR   : {u v : RTm} → K · u · v ↦ u
  SβR   : {u v w : RTm} → S · u · v · w ↦ u · w · (v · w)
  _·_  : {t₀ t₁ u₀ u₁ : RTm} → t₀ ↦ t₁ → u₀ ↦ u₁ → t₀ · u₀ ↦ t₁ · u₁
  ↦Prop : ∀{u v} → isProp (u ↦ v)

data _↦*_ : RTm → RTm → Set where
  refl* : {u : RTm} → u ↦* u
  step : {u₀ u₁ u₂ : RTm} → u₀ ↦ u₁ → u₁ ↦* u₂ → u₀ ↦* u₂

_~_ : RTm → RTm → Set
t₀ ~ t₁ = Σ RTm λ t → (t₀ ↦* t) × (t₁ ↦* t)

ref~ : {t : RTm} → t ~ t
ref~ {t} = t , refl* , refl*

·-right : {t u₀ u₁ : RTm} → u₀ ↦* u₁ → t · u₀ ↦* t · u₁
·-right refl* = refl*
·-right (step u₀u₁ u₁u₂) = step (idR · u₀u₁) (·-right u₁u₂)

·-left : {u₀ u₁ t : RTm} → u₀ ↦* u₁ → u₀ · t ↦* u₁ · t
·-left refl* = refl*
·-left (step u₀u₁ u₁u₂) = step (u₀u₁ · idR) (·-left u₁u₂)

M : Model
M = record {
  Tm = RTm / _~_ ;
  TmSet = squash/ ;
  _·_ = λ a b → rec squash/ (λ t → rec squash/ (λ u → [ t · u ]) {!!} b) {!!} a ;
  K = [ K ] ; S = [ S ] ;
  Kβ = {!!} ;
  Sβ = {!!} }
