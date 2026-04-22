{-# OPTIONS --prop --rewriting --with-K --no-postfix-projections #-}

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
  instance refl : a ~ a

~ₑ : (A : Set i)(a : A)(B : Set i)(b : B) → Prop i
~ₑ _ a _ b = a ~ b

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

  coh : {e : A₀ ~ A₁} → a₀ ~ coe e a₀
  coh {e = refl} = refl

infix 4 _~[_]_
_~[_]_ : {A₀ A₁ : Set i} → A₀ → A₀ ~ A₁ → A₁ → Prop i
a₀ ~[ e ] a₁ = a₀ ~ a₁

infix 4 _≈_
_≈_ : {A : Set i} → A → A → Prop i
a₀ ≈ a₁ = a₀ ~ a₁

postulate
  Π-inj₁ : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j} → Π' A₀ B₀ ~ Π' A₁ B₁ → A₀ ~ A₁
  Π-inj₂ : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j} → Π' A₀ B₀ ~ Π' A₁ B₁ → ∀{a₀ a₁} → (a₀ ~ a₁) → B₀ a₀ ~ B₁ a₁
  coe'-Π : {A₀ A₁ : Set i}{B₀ : A₀ → Set j}{B₁ : A₁ → Set j}{e : Π' A₀ B₀ ~ Π' A₁ B₁}{f₀ : Π' A₀ B₀} →
    coe' e f₀ ↝ λ a₁ → coe (Π-inj₂ e (sym coh)) (f₀ (coe (sym (Π-inj₁ e)) a₁))
  {-# REWRITE coe'-Π #-}
  funextₕ : (e : A₀ ≈ A₁){B₀ : A₀ → Set j}{B₁ : A₁ → Set j}{f₀ : Π' A₀ B₀}{f₁ : Π' A₁ B₁} → (∀{a₀ a₁} → a₀ ~[ e ] a₁ → f₀ a₀ ~ f₁ a₁) → f₀ ~ f₁

funext : {B₀ B₁ : A₀ → Set j}{f₀ : Π' A₀ B₀}{f₁ : Π' A₀ B₁} → (∀{a₀} → f₀ a₀ ~ f₁ a₀) → f₀ ~ f₁
funext {i} {A₀} {j} {B₀} {B₁} {f₀} {f₁} f = funextₕ {i} {A₀} {A₀} {j} refl {B₀} {B₁} {f₀} {f₁} λ {a₀} → λ {refl → f {a₀}}

_$'_ : {B₀ B₁ : A → Set j} → B₀ ~ B₁ → {f₀ : Π' A B₀}{f₁ : Π' A B₁} → f₀ ~ f₁ → ∀{a} → f₀ a ~ f₁ a
_$'_ refl e {a} = congₕ (λ f → f a) e

toTy~ : {a₀ : A₀}{a₁ : A₁} → a₀ ~ a₁ → A₀ ~ A₁
toTy~ refl = refl

infixl 4.5 _$_
_$_ : {B₀ : A₀ → Set j}{B₁ : A₁ → Set j}{f₀ : Π' A₀ B₀}{f₁ : Π' A₁ B₁} → f₀ ~ f₁ → ∀{a₀ a₁} → a₀ ~ a₁ → f₀ a₀ ~ f₁ a₁
e $ refl = funext (Π-inj₂ (toTy~ e) refl) $' e

infixl 4.5 _⠀_
_⠀_ = _$_

cong : (a : A) → a ~ a
cong a = refl

infixr 4.75 _∎
_∎ : (a : A) → a ~ a
_ ∎ = refl

the : (A : Set i) → A → A
the _ a = a

----------------------
-- Metatheory types --
----------------------

module L where

  data ⊥ : Set where

  record ⊤ : Set where
    instance constructor tt

  open ⊤ public

  data Bool : Set where
    false true : Bool

  infixr 4 _,_
  record Σ {i}{j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

open L

record Lift {i}(A : Prop i) : Set i where
  instance constructor mk
  field
    ⦃ un ⦄ : A

open Lift {{...}} public

mkₑ : ∀{i}{A : Prop i} → A → Lift A
mkₑ a = mk ⦃ a ⦄

infixr 1.75 _,-
pattern _,- i ⦃ e ⦄ = _,_ i (mk ⦃ e ⦄)

infixr 1.75 _,ₚ_
pattern _,ₚ_ i e = _,_ i (mk ⦃ e ⦄)

infix 0 Σ-syntax

Σ-syntax : ∀{a b}(A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = [ x ∶ A ] × B

∃P : ∀ {a b}(A : Set a) → (A → Prop b) → Set (a ⊔ b)
∃P A B = Σ A (λ a → Lift (B a))

infix 0 ∃P-syntax

∃P-syntax : ∀ {a b}(A : Set a) → (A → Prop b) → Set (a ⊔ b)
∃P-syntax = ∃P

syntax ∃P-syntax A (λ x → B) = ∃[ x ∶ A ] B

∃ : ∀ {a b}{A : Set a} → (A → Prop b) → Set (a ⊔ b)
∃ B = Σ _ (λ a → Lift (B a))

infix 0 ∃-syntax

∃-syntax : ∀ {a b}{A : Set a} → (A → Prop b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

Σ-extₕ :
  {B₀ : A₀ → Set i} {B₁ : A₁ → Set i} {t₀ : Σ A₀ B₀} {t₁ : Σ A₁ B₁} →
  (e1 : fst t₀ ~ fst t₁)(e2 : B₀ ~[ cong (λ A → A → Set i) $ toTy~ e1 ] B₁) → snd t₀ ~[ e2 $ e1 ] snd t₁ → t₀ ~ t₁
Σ-extₕ e1 e2 e3 = cong (λ x y → L._,_ {_} {_} {x} {y}) $ toTy~ e1 $ e2 $ e1 $ e3

Σ-extₚ :
  {B₀ : A₀ → Prop i} {B₁ : A₁ → Prop i} {t₀ : ∃P A₀ B₀} {t₁ : ∃P A₁ B₁} →
  (e1 : fst t₀ ~ fst t₁)(e₂ : B₀ ~[ cong (λ A → A → Prop i) $ toTy~ e1 ] B₁) → t₀ ~ t₁
Σ-extₚ refl refl = refl

_,Σ≈_ : ∀{i j}{A : Set i}{B : A → Set j}{a : A}{b : B a}{c : A}{d : B c}(e : a ≈ c) → b ~[ cong B $ e ] d → (a L., b) ≈ (c L., d)
e1 ,Σ≈ e2 = cong L._,_ $ e1 $ e2

_,Σ≈- : ∀{i j}{A : Set i}{B : A → Prop j}{a : A}{b : B a}{c : A}{d : B c}(e : a ≈ c) → (a L., mkₑ b) ≈ (c L., mkₑ d)
refl ,Σ≈- = refl ,Σ≈ refl

it : ∀{i}{A : Prop i} → ⦃ A ⦄ → A
it ⦃ a ⦄ = a
