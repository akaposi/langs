{-# OPTIONS --prop --rewriting --with-K #-}

module Lib where

open import Agda.Primitive public

private variable
  i j k l : Level
  A A₀ A₁ A₂ : Set i
  a a₀ a₁ a₂ : A

infix 4 _↝_
postulate
  _↝_ : {A : Set i} → A → A → Prop
{-# BUILTIN REWRITE _↝_ #-}

infix 4 _~_
data _~_ {A : Set i}(a : A) : {B : Set i} → B → Prop i where
  refl : a ~ a

sym : {a₀ : A₀}{a₁ : A₁} → a₀ ~ a₁ → a₁ ~ a₀
sym refl = refl

infixr 2 _∙_
_∙_ : {a₀ : A₀}{a₁ : A₁}{a₂ : A₂} → a₀ ~ a₁ → a₁ ~ a₂ → a₀ ~ a₂
refl ∙ e = e

Π' : (A : Set i) → (A → Set j) → Set _
Π' A B = (a : A) → B a

congₕ : {B₀ : A₀ → Set j}(f : Π' A₀ B₀) → a₀ ~ a₁ → f a₀ ~ f a₁
congₕ _ refl = refl

postulate
  coe' : A₀ ~ A₁ → A₀ → A₁
  coe'-refl : coe' refl a ↝ a
  {-# REWRITE coe'-refl #-}

opaque
  coe : A₀ ~ A₁ → A₀ → A₁
  coe = coe'

  coh : {e : A₀ ~ A₁} → coe e a₀ ~ a₀
  coh {e = refl} = refl

postulate
  Π-inj₁ : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j} → Π' A₀ B₀ ~ Π' A₁ B₁ → A₀ ~ A₁
  Π-inj₂ : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j} → Π' A₀ B₀ ~ Π' A₁ B₁ → ∀{a₀ a₁} → (a₀ ~ a₁) → B₀ a₀ ~ B₁ a₁
  coe'-Π : {A₀ A₁ : Set i}{B₀ : A₀ → Set j}{B₁ : A₁ → Set j}{e : Π' A₀ B₀ ~ Π' A₁ B₁}{f₀ : Π' A₀ B₀} →
    coe' e f₀ ↝ λ a₁ → coe (Π-inj₂ e coh) (f₀ (coe (sym (Π-inj₁ e)) a₁))
  {-# REWRITE coe'-Π #-}
  funext : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}{f₀ : Π' A₀ B₀}{f₁ : Π' A₁ B₁} → (∀{a₀ a₁} → a₀ ~ a₁ → f₀ a₀ ~ f₁ a₁) → f₀ ~ f₁

_$'_ : {B₀ B₁ : A → Set j} → B₀ ~ B₁ → {f₀ : Π' A B₀}{f₁ : Π' A B₁} → f₀ ~ f₁ → ∀{a} → f₀ a ~ f₁ a
_$'_ refl e {a} = congₕ (λ f → f a) e

toTy~ : {a₀ : A₀}{a₁ : A₁} → a₀ ~ a₁ → A₀ ~ A₁
toTy~ refl = refl

infixl 4.5 _$_
_$_ : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}{f₀ : Π' A₀ B₀}{f₁ : Π' A₁ B₁} → f₀ ~ f₁ → ∀{a₀ a₁} → a₀ ~ a₁ → f₀ a₀ ~ f₁ a₁
e $ refl = funext (Π-inj₂ (toTy~ e)) $' e

infixl 4.5 _⠀_
_⠀_ = _$_

infix 4 _~[_]_
_~[_]_ : {A₀ A₁ : Set i} → A₀ → A₀ ~ A₁ → A₁ → Prop i
a₀ ~[ e ] a₁ = a₀ ~ a₁

infix 4 _≈_
_≈_ : {A : Set i} → A → A → Prop i
a₀ ≈ a₁ = a₀ ~ a₁

cong : (a : A) → a ~ a
cong a = refl

infixr 4.75 _∎
_∎ : (a : A) → a ~ a
_ ∎ = refl

the : (A : Set i) → A → A
the _ a = a
