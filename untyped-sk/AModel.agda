{-# OPTIONS
  --safe
  --cubical
  --no-import-sorts
  --postfix-projections
  -WnoUnsupportedIndexedMatch
#-}

module untyped-sk.AModel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation as T
open import Cubical.HITs.SetQuotients.Base
import Cubical.HITs.SetQuotients as Q
open Iso
open BinaryRelation
open isEquivRel

open import untyped-sk.Model
open import untyped-sk.Syntax as I

infixl 5 _·_
data RTm : Type where
  K S : RTm
  _·_ : RTm → RTm → RTm

private variable
  x x′ y y′ z z′ : RTm

-- one-step parallel rewriting
infix 4 _↝_
data _↝_ : RTm → RTm → Type where
  K : K ↝ K
  S : S ↝ S
  _·_ : (x ↝ x′) → (y ↝ y′) → (x · y ↝ x′ · y′)
  Kβ : (x ↝ x′) → (K · x · y ↝ x′)
  Sβ : (x ↝ x′) → (y ↝ y′) → (z ↝ z′) → (S · x · y · z ↝ x′ · z′ · (y′ · z′))

refl↝ : x ↝ x
refl↝ {K} = K
refl↝ {S} = S
refl↝ {x · y} = refl↝ · refl↝

-- its reflexive transitive closure
infix 4 _↝*_
infixr 9 _∷*_
data _↝*_ : RTm → RTm → Type where
  refl* : x ↝* x
  _∷*_ : (x ↝ y) → (y ↝* z) → (x ↝* z)

[_]* : (x ↝ y) → (x ↝* y)
[ x↝y ]* = x↝y ∷* refl*

infixr 9 _∙*_
_∙*_ : (x ↝* y) → (y ↝* z) → (x ↝* z)
refl* ∙* x↝*y = x↝*y
(x↝y ∷* y↝*z) ∙* z↝*t = x↝y ∷* y↝*z ∙* z↝*t

infixl 10 _·*_
_·*_ : (x ↝* x′) → (y ↝* y′) → (x · y ↝* x′ · y′)
refl* ·* refl* = refl*
refl* ·* (y↝y′ ∷* y′↝*y″) = (refl↝ · y↝y′) ∷* (refl* ·* y′↝*y″)
(x↝x′ ∷* x′↝x″) ·* y↝*y′ = (x↝x′ · refl↝) ∷* (x′↝x″ ·* y↝*y′)

-- approach from PLFA
-- https://plfa.github.io/Confluence/#parallel-reduction-satisfies-the-diamond-property
-- maximum one-step parallel reduction
step : RTm → RTm
step K = K
step S = S
step (K · x · y) = step x
step (S · x · y · z) = step x · step z · (step y · step z)
{-# CATCHALL #-}
step (x · y) = step x · step y

↝step : (x ↝ y) → (y ↝ step x)
↝step K = K
↝step S = S
↝step (_·_ {x = K} K↝x′ y↝y′) = ↝step K↝x′ · ↝step y↝y′
↝step (_·_ {x = S} S↝x′ y↝y′) = ↝step S↝x′ · ↝step y↝y′
↝step (_·_ {x = K · x} (K · x↝x′) y↝y′) = Kβ (↝step x↝x′)
↝step (_·_ {x = S · x} Sx↝x′ y↝y′) = ↝step Sx↝x′ · ↝step y↝y′
↝step (_·_ {x = K · x · y} Kxy↝x′ z↝z′) = ↝step Kxy↝x′ · ↝step z↝z′
↝step (_·_ {x = S · x · y} (S · x↝x′ · y↝y′) z↝z′) =
  Sβ (↝step x↝x′) (↝step y↝y′) (↝step z↝z′)
↝step (_·_ {x = x · y · z · t} xyzt↝x′ u↝u′) = ↝step xyzt↝x′ · ↝step u↝u′
↝step (Kβ x↝x′) = ↝step x↝x′
↝step (Sβ x↝x′ y↝y′ z↝z′) =
  ↝step x↝x′ · ↝step z↝z′ · (↝step y↝y′ · ↝step z↝z′)


↝confl : (x ↝ y) → (x ↝ y′) → Σ[ z ∈ RTm ] (y ↝ z) × (y′ ↝ z)
↝confl x↝y x↝y′ = _ , ↝step x↝y , ↝step x↝y′

↝*conflᵣ : (x ↝ y) → (x ↝* y′) → Σ[ z ∈ RTm ] (y ↝* z) × (y′ ↝ z)
↝*conflᵣ x↝y refl* = _ , refl* , x↝y
↝*conflᵣ x↝y (x↝y′ ∷* y′↝*z′) = let
  _ , y↝z , y′↝z = ↝confl x↝y x↝y′
  _ , z↝*t , z′↝t = ↝*conflᵣ y′↝z y′↝*z′
  in _ , y↝z ∷* z↝*t , z′↝t

↝*confl : (x ↝* y) → (x ↝* y′) → Σ[ z ∈ RTm ] (y ↝* z) × (y′ ↝* z)
↝*confl refl* x↝*y′ = _ , x↝*y′ , refl*
↝*confl (x↝y ∷* y↝*z) x↝*y′ = let
  _ , y↝*z′ , y′↝z′ = ↝*conflᵣ x↝y x↝*y′
  _ , z↝*t , z′↝*t = ↝*confl y↝*z y↝*z′
  in _ , z↝*t , y′↝z′ ∷* z′↝*t

infix 4 _~_
_~_ : RTm → RTm → Type
x ~ y = Σ[ z ∈ RTm ] (x ↝* z) × (y ↝* z)

refl~ : x ~ x
refl~ = _ , refl* , refl*

sym~ : x ~ y → y ~ x
sym~ (_ , x↝*z , y↝*z) = _ , y↝*z , x↝*z

infixr 9 _∙~_
_∙~_ : x ~ y → y ~ z → x ~ z
_∙~_ (_ , x↝*t , y↝*t) (_ , y↝*u , z↝*u) = let
  _ , t↝*v , u↝*v = ↝*confl y↝*t y↝*u
  in _ , x↝*t ∙* t↝*v , z↝*u ∙* u↝*v

isEquiv~ : isEquivRel _~_
isEquiv~ .reflexive x = refl~
isEquiv~ .symmetric x y = sym~
isEquiv~ .transitive x y z = _∙~_

Tmᴹ : Type
Tmᴹ = RTm / _~_

isSetTmᴹ : isSet Tmᴹ
isSetTmᴹ = squash/

Kᴹ : Tmᴹ
Kᴹ = [ K ]

Sᴹ : Tmᴹ
Sᴹ = [ S ]

infixl 10 _·ᴹ_
_·ᴹ_ : Tmᴹ → Tmᴹ → Tmᴹ
_·ᴹ_ =
  Q.setQuotBinOp (λ x → refl~) (λ y → refl~) _·_
    λ x₀ x₁ y₀ y₁ (x′ , x₀↝*x′ , x₁↝*x′) (y′ , y₀↝*y′ , y₁↝*y′) →
      x′ · y′ , x₀↝*x′ ·* y₀↝*y′ , x₁↝*x′ ·* y₁↝*y′

Kβᴹ : ∀ x y → Kᴹ ·ᴹ x ·ᴹ y ≡ x
Kβᴹ = Q.elimProp2 (λ x y → isSetTmᴹ _ _) λ x y →
  eq/ _ _ (x , [ Kβ refl↝ ]* , refl*)

Sβᴹ : ∀ x y z → Sᴹ ·ᴹ x ·ᴹ y ·ᴹ z ≡ x ·ᴹ z ·ᴹ (y ·ᴹ z)
Sβᴹ = Q.elimProp3 (λ x y z → isSetTmᴹ _ _) λ x y z →
  eq/ _ _ (x · z · (y · z) , [ Sβ refl↝ refl↝ refl↝ ]* , refl*)

M : Model
M .Model.Tm = Tmᴹ
M .Model.TmSet = isSetTmᴹ
M .Model.K = Kᴹ
M .Model.S = Sᴹ
M .Model._·_ = _·ᴹ_
M .Model.Kβ {x}{y} = Kβᴹ x y
M .Model.Sβ {x}{y}{z} = Sβᴹ x y z

module M = Model M

K≢S : ¬ K ≡ S
K≢S p = subst P p tt
  where
  P : RTm → Type
  P K = Unit
  P S = ⊥
  P (x · y) = Unit

K↝ : (K ↝ x) → x ≡ K
K↝ K = refl

S↝ : (S ↝ x) → x ≡ S
S↝ S = refl

K↝* : (x ↝* y) → x ≡ K → y ≡ K
K↝* refl* p = p
K↝* (x↝y ∷* y↝*z) p = K↝* y↝*z (K↝ (subst (_↝ _) p x↝y))

S↝* : (x ↝* y) → x ≡ S → y ≡ S
S↝* refl* p = p
S↝* (x↝y ∷* y↝*z) p = S↝* y↝*z (S↝ (subst (_↝ _) p x↝y))

K≁S : ¬ K ~ S
K≁S (_ , x↝*z , y↝*z) = K≢S (sym (K↝* x↝*z refl) ∙ S↝* y↝*z refl)

Kᴹ≢Sᴹ : ¬ Kᴹ ≡ Sᴹ
Kᴹ≢Sᴹ p = T.rec isProp⊥ K≁S (Q.isEquivRel→TruncIso isEquiv~ _ _ .fun p)

IK≢S : ¬ I.K ≡ I.S
IK≢S p = Kᴹ≢Sᴹ (cong M.⟦_⟧ p)
