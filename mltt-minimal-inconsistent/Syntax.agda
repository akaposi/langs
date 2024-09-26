{-# OPTIONS --cubical #-}
-- {-# OPTIONS --allow-unsolved-metas #-} 

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)

module mltt-minimal-inconsistent.Syntax where

infixl 4 _▹_
infixl 8 _∘_ _∘'_ _∘*_
infixl 10 _⁺ _⁺' _⁺*

data Con : Type
data Sub : Con → Con → Type
data Ty  : Con → Type
data Tm  : (Γ : Con) → Ty Γ → Type

private variable
  Γ Δ Θ Ξ : Con
  γ δ θ ξ σ γa : Sub Δ Γ
  A B C : Ty Γ
  a b c Â t : Tm Γ A

data Con where
  _▹_ : (Γ : Con) → Ty Γ → Con
  ◇   : Con

_∘'_   : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
id'    : Sub Γ Γ

_[_]T'    : Ty Γ → Sub Δ Γ → Ty Δ

p'     : Sub (Γ ▹ A) Γ
⟨_⟩'   : Tm Γ A → Sub Γ (Γ ▹ A)
_⁺'    : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T') (Γ ▹ A)
_[_]t' : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T')
U'     : Ty Γ

data Ty where
  TySet    : isSet (Ty Γ)
  _[_]T    : Ty Γ → Sub Δ Γ → Ty Δ
  [∘]T     : A [ γ ∘' δ ]T ≡ A [ γ ]T [ δ ]T
  [id]T    : A [ id' ]T ≡ A
  [p][⟨⟩]T : {A : Ty Γ}{b : Tm Γ B} → A [ p' ]T [ ⟨ b ⟩' ]T ≡ A
  [p][⁺]T  : A [ p' {A = B} ]T [ γ ⁺' ]T ≡ A [ γ ]T [ p' ]T
  
  U        : Ty Γ
  U[]      : U [ γ ]T ≡ U
  El       : Tm Γ U' → Ty Γ
  
  Π        : (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
  Π[]      : Π A B [ γ ]T ≡ Π (A [ γ ]T') (B [ γ ⁺' ]T)

_[_]T' = _[_]T
U'      = U

q'     : Tm (Γ ▹ A) (A [ p' ]T)

data Sub where
  SubSet : isSet (Sub Δ Γ)
  _∘_    : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  ass    : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
  id     : Sub Γ Γ
  idl    : id ∘ γ ≡ γ
  idr    : γ ∘ id ≡ γ
  ε      : Sub Γ ◇
  ◇η     : σ ≡ ε
  p      : Sub (Γ ▹ A) Γ
  _⁺     : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
  ⟨_⟩    : Tm Γ A → Sub Γ (Γ ▹ A)
  ∘⁺     : PathP (λ i → Sub (Θ ▹ [∘]T {A = A}{γ = γ}{δ = δ} i) (Γ ▹ A)) ((γ ∘' δ) ⁺) (γ ⁺ ∘' δ ⁺)
  id⁺    : PathP (λ i → Sub (Γ ▹ [id]T {A = A} i) (Γ ▹ A)) (id' ⁺) id'
  p∘⁺    : p {A = A} ∘ γ ⁺ ≡ γ ∘ p
  p∘⟨⟩   : p ∘ ⟨ a ⟩ ≡ id
  ⟨⟩∘    : ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]t' ⟩
  p⁺∘⟨q⟩ : p' ⁺ ∘ ⟨ q' ⟩ ≡ id {Γ ▹ A}

_∘'_ = _∘_
id'  = id
p'   = p
⟨_⟩' = ⟨_⟩
_⁺'  = _⁺

data Tm where
  TmSet : isSet (Tm Γ A)
  _[_]t : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
  q     : Tm (Γ ▹ A) (A [ p ]T)
  q[⟨⟩] : PathP (λ i → Tm Γ ([p][⟨⟩]T {A = A}{b = a} i)) (q [ ⟨ a ⟩ ]t) a
  q[⁺]  : PathP (λ i → Tm (Δ ▹ A [ γ ]T) ([p][⁺]T {A = A} i)) (q [ γ ⁺ ]t) q
  [∘]t  : PathP (λ i → Tm Θ ([∘]T {A = A}{γ = γ}{δ = δ} i)) (a [ γ ∘ δ ]t) (a [ γ ]t [ δ ]t)
  [id]t : PathP (λ i → Tm Γ ([id]T {A = A} i)) (a [ id ]t) a

  cd    : Ty Γ → Tm Γ U
  cd[]  : PathP (λ i → Tm Δ (U[] {γ = γ} i)) (cd A [ γ ]t) (cd (A [ γ ]T))

  lam   : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → Tm (Γ ▹ A) B
  Πβ    : app (lam b) ≡ b
  Πη    : lam (app t) ≡ t
  lam[] : PathP (λ i → Tm Γ (Π[] {B = B}{γ = γ} i)) (lam b [ γ ]t) (lam (b [ γ ⁺ ]t))

_[_]t' = _[_]t
q'     = q

-- defined stuff

_[_]Π : Tm Γ (Π A B) → (γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
t [ γ ]Π = subst (Tm _) Π[] (t [ γ ]t)

app[] : app t [ γ ⁺ ]t ≡ app (t [ γ ]Π)
app[] = {!!}
-- app t[γ⁺] =(β) app(lam(app t[γ⁺])) =(lam[]) app(lam(app t)[γ]) =(η) = app(t[γ])

El[] : El Â [ γ ]T ≡ El (subst (Tm Δ) U[] (Â [ γ ]t))
El[] = {!!}

-- CwF combinators:

-- TODO: γ ,Tm a := γ ⁺ ∘ ⟨ a ⟩
-- TODO: prove the CwF laws ▹β₁, ▹β₂, ▹η
