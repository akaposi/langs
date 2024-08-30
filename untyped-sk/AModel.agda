{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Empty renaming (rec to exfalso) hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import untyped-sk.Model

module untyped-sk.AModel where

infixl 5 _·_ _·'_
infix  4 _↦_ _↦*_

data RTm : Set where
  S K : RTm
  _·_ : RTm → RTm → RTm

-- one-step parallel rewriting with identity
data _↦_ : RTm → RTm → Set where
  idR   : {u : RTm} → u ↦ u
  KβR   : {u v : RTm} → K · u · v ↦ u
  SβR   : {u v w : RTm} → S · u · v · w ↦ u · w · (v · w)
  _·_   : {t₀ t₁ u₀ u₁ : RTm} → t₀ ↦ t₁ → u₀ ↦ u₁ → t₀ · u₀ ↦ t₁ · u₁
  ↦Prop : ∀{u v} → isProp (u ↦ v)

-- its reflexive transitive closure
data _↦*_ : RTm → RTm → Set where
  refl* : {u : RTm} → u ↦* u
  step : {u₀ u₁ u₂ : RTm} → u₀ ↦ u₁ → u₁ ↦* u₂ → u₀ ↦* u₂

-- this will be our equivalence relation
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

-- a congruence rule
rec= : ∀{ℓ}{A : Set ℓ}{Aset : isSet A}{f f' : RTm → A} → 
  {e : (t₀ t₁ : RTm) → t₀ ~ t₁ → f t₀ ≡ f t₁}
  {e' : (t₀ t₁ : RTm) → t₀ ~ t₁ → f' t₀ ≡ f' t₁}
  {b : RTm / _~_} → (f= : f ≡ f') →
  rec Aset f e b ≡ rec Aset f' e' b
rec= {ℓ}{A}{Aset}{f}{f'}{e}{e'}{b} f= = rec=' {ℓ}{A}{Aset}{f}{f'}{e}{e'}{b} f= (e= {Aset = Aset} f=)
  where
    rec=' : ∀{ℓ}{A : Set ℓ}{Aset : isSet A}{f f' : RTm → A} → 
      {e : (t₀ t₁ : RTm) → t₀ ~ t₁ → f t₀ ≡ f t₁}
      {e' : (t₀ t₁ : RTm) → t₀ ~ t₁ → f' t₀ ≡ f' t₁}
      {b : RTm / _~_} → (f= : f ≡ f') →
      PathP (λ i → (t₀ t₁ : RTm) → t₀ ~ t₁ → f= i t₀ ≡ f= i t₁) e e' →
      rec Aset f e b ≡ rec Aset f' e' b
    rec=' {Aset = Aset}{b = b} f= e= i = rec Aset (f= i) (e= i) b

    e= : ∀{ℓ}{A : Set ℓ}{Aset : isSet A}{f f' : RTm → A} → 
      {e : (t₀ t₁ : RTm) → t₀ ~ t₁ → f t₀ ≡ f t₁}
      {e' : (t₀ t₁ : RTm) → t₀ ~ t₁ → f' t₀ ≡ f' t₁}
      (f= : f ≡ f') →
      PathP (λ i → (t₀ t₁ : RTm) → t₀ ~ t₁ → f= i t₀ ≡ f= i t₁) e e'
    e= {Aset = Aset}{f}{f'}{e}{e'} f= = J
      (λ f' f= → (e' : (t₀ t₁ : RTm) → t₀ ~ t₁ → f' t₀ ≡ f' t₁) → PathP (λ i → (t₀ t₁ : RTm) → t₀ ~ t₁ → f= i t₀ ≡ f= i t₁) e e')
      (λ e' i t₀ t₁ t₀t₁ → Aset (f t₀) (f t₁) (e t₀ t₁ t₀t₁) (e' t₀ t₁ t₀t₁) i)
      f= e'

Tm = RTm / _~_

_·'_ : Tm → Tm → Tm
a ·' b = rec squash/
  (λ t → rec squash/ (λ u → [ t · u ]) (λ { u₀ u₁ (u , u₀u , u₁u) → eq/ _ _ (t · u , ·-right u₀u , ·-right u₁u) }) b)
  (λ { t₀ t₁ (t , t₀t , t₁t) → rec= {Aset = squash/}{f = (λ u → [ t₀ · u ])}{λ u → [ t₁ · u ]}
    {λ { u₀ u₁ (u , u₀u , u₁u) → eq/ _ _ (t₀ · u , ·-right u₀u , ·-right u₁u) }}
    {λ { u₀ u₁ (u , u₀u , u₁u) → eq/ _ _ (t₁ · u , ·-right u₀u , ·-right u₁u) }}
    {b}
    λ i u → eq/ (t₀ · u) (t₁ · u) (t · u , ·-left t₀t , ·-left t₁t) i})
  a

Kβ : {a b : Tm} → [ K ] ·' a ·' b ≡ a
Kβ {a}{b} = elim {P = λ a → [ K ] ·' a ·' b ≡ a}
  (λ x → isProp→isSet (squash/ ([ K ] ·' x ·' b) x))
  (λ t → elim {P = λ b → (([ K ] ·' [ t ]) ·' b) ≡ [ t ]}
    (λ x → isProp→isSet (squash/ ([ K ] ·' [ t ] ·' x) [ t ]))
    (λ u → eq/ _ _ (t , step KβR refl* , step idR refl*))
    (λ _ _ _ → toPathP (squash/ _ _ _ _))
    b)
  (λ _ _ _ → toPathP (squash/ _ _ _ _))
  a

Sβ : {a b c : Tm} → [ S ] ·' a ·' b ·' c ≡ a ·' c ·' (b ·' c)
Sβ {a}{b}{c} = elim {P = λ a → [ S ] ·' a ·' b ·' c ≡ a ·' c ·' (b ·' c)}
  (λ x → isProp→isSet (squash/ ([ S ] ·' x ·' b ·' c) (x ·' c ·' (b ·' c))))
  (λ t → elim {P = λ b → [ S ] ·' [ t ] ·' b ·' c ≡ [ t ] ·' c ·' (b ·' c)}
    (λ x → isProp→isSet (squash/ ([ S ] ·' [ t ] ·' x ·' c) ([ t ] ·' c ·' (x ·' c))))
    (λ u → elim {P = λ c → [ S ] ·' [ t ] ·' [ u ] ·' c ≡ [ t ] ·' c ·' ([ u ] ·' c)}
      (λ x → isProp→isSet (squash/ ([ S ] ·' [ t ] ·' [ u ] ·' x) ([ t ] ·' x ·' ([ u ] ·' x))))
      (λ v → eq/ _ _ (t · v · (u · v) , step SβR refl* , step idR refl*))
      (λ _ _ _ → toPathP (squash/ _ _ _ _))
      c)
    (λ _ _ _ → toPathP (squash/ _ _ _ _))
    b)
  (λ _ _ _ → toPathP (squash/ _ _ _ _))
  a

M : Model
M = record {
  Tm = Tm ;
  TmSet = squash/ ;
  _·_ = _·'_ ;
  K = [ K ] ; S = [ S ] ;
  Kβ = λ {a}{b} → Kβ {a}{b} ;
  Sβ = λ {a}{b}{c} → Sβ {a}{b}{c} }

module M = Model M

-- we want to prove that K ≠ S in this model, and hence in the syntax

-- boilerplate for RTm
S≠K : S ≡ K → ⊥
S≠K e = transport (cong (λ { K → ⊥ ; _ → Unit } ) e) _
K≠· : ∀{u v} → K ≡ u · v → ⊥
K≠· e = transport (cong (λ { (u · v) → ⊥ ; _ → Unit } ) e) _
S≠· : ∀{u v} → S ≡ u · v → ⊥
S≠· e = transport (cong (λ { (u · v) → ⊥ ; _ → Unit } ) e) _
inj·₁ : ∀{u v u' v' : RTm} → u · v ≡ u' · v' → u ≡ u'
inj·₁ e = cong (λ { (u · v) → u ; _ → K } ) e
inj·₂ : ∀{u v u' v' : RTm} → u · v ≡ u' · v' → v ≡ v'
inj·₂ e = cong (λ { (u · v) → v ; _ → K } ) e
RTmSet : isSet RTm
RTmSet = Discrete→isSet discrete
  where
    discrete : (u v : RTm) → Dec (u ≡ v)
    discrete S S = yes refl
    discrete S K = no S≠K
    discrete S (_ · _) = no S≠·
    discrete K S = no λ e → S≠K (sym e)
    discrete K K = yes refl
    discrete K (_ · _) = no K≠·
    discrete (_ · _) S = no λ e → S≠· (sym e)
    discrete (_ · _) K = no λ e → K≠· (sym e)
    discrete (u · v) (u' · v') with discrete u u' | discrete v v'
    ... | yes e | yes e' = yes (cong₂ _·_ e e')
    ... | yes _ | no ¬e = no λ e → ¬e (inj·₂ e)
    ... | no ¬e | yes _ = no λ e → ¬e (inj·₁ e)
    ... | no ¬e | no  _ = no λ e → ¬e (inj·₁ e)

Sval' : ∀{t} → S ↦ t → t ≡ S
Sval' idR = refl
Sval' (↦Prop St St' i) j = {!!}

Sval : ∀{t} → S ↦* t → t ≡ S
Sval refl* = refl
Sval {t} (step St e) = {!!}

Kval : ∀{t} → K ↦* t → t ≡ K
Kval refl* = refl
Kval (step idR e) = Kval e

S≁K : S ~ K → ⊥
S≁K (t , St , Kt) = S≠K (sym (Sval St) ∙ Kval Kt)

sym~ : ∀{u v} → u ~ v → v ~ u
sym~ e = {!!}

trans~ : ∀{u v w} → u ~ v → v ~ w → u ~ w
trans~ e e' = {!!}

[S]≠[K] : [ RTm.S ] ≡ [ K ] → ⊥
[S]≠[K] e = S≁K (effective {R = _~_} {!!} (BinaryRelation.equivRel (λ _ → ref~) (λ _ _ → sym~) λ _ _ _ → trans~) _ _ e)

open import untyped-sk.Syntax

-- K ≠ S in the syntax
K≠S : Tm.K ≡ S → ⊥
K≠S e = [S]≠[K] (sym (cong M.⟦_⟧ e))
