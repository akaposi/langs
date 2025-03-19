{-# OPTIONS --cubical #-}
-- {-# OPTIONS --allow-unsolved-metas #-} 

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)

module mltt-minimal.Syntax where

infixl 5 _▹_
infixl 8 _∘_ _∘'_ _∘*_
infixl 9 _[_]T _[_]T' _[_]t _[_]t' _[_]T* _[_]t* _[_]U _[_]U' _[_]T= _[_]t=
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
_[_]U' : Tm Γ U' → (γ : Sub Δ Γ) → Tm Δ U'
q'     : Tm (Γ ▹ A) (A [ p' ]T')

data Ty where
  TySet      : isSet (Ty Γ)
  _[_]T      : Ty Γ → Sub Δ Γ → Ty Δ
  [∘]T       : A [ γ ∘' δ ]T ≡ A [ γ ]T [ δ ]T
  [id]T      : A [ id' ]T ≡ A
  [p][⟨⟩]T   : {A : Ty Γ}{b : Tm Γ B} → A [ p' ]T [ ⟨ b ⟩' ]T ≡ A
  [p][⁺]T    : A [ p' {A = B} ]T [ γ ⁺' ]T ≡ A [ γ ]T [ p' ]T
  [p⁺][⟨q⟩]T : A ≡ A [ p' ⁺' ]T [ ⟨ q' ⟩' ]T
  [⟨⟩][]T    : A [ ⟨ a ⟩' ]T [ γ ]T ≡ A [ γ ⁺' ]T [ ⟨ a [ γ ]t' ⟩' ]T

  
  U        : Ty Γ
  U[]      : U [ γ ]T ≡ U
  El       : Tm Γ U' → Ty Γ
  El[]     : El Â [ γ ]T ≡ El (Â [ γ ]U')
  
  Π        : (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
  Π[]      : Π A B [ γ ]T ≡ Π (A [ γ ]T') (B [ γ ⁺' ]T)

_[_]T' = _[_]T
U'      = U

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
  p⁺∘⟨q⟩ : id {Γ ▹ A} ≡ p' ⁺ ∘ ⟨ q' ⟩

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

  _[_]U : Tm Γ U → (γ : Sub Δ Γ) → Tm Δ U
  []U   : PathP (λ i → Tm Δ (U[] {γ = γ} i)) (Â [ γ ]t) (Â [ γ ]U)

  _[_]Π : Tm Γ (Π A B) → (γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
  lam   : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
  Πβ    : app (lam b) a ≡ b [ ⟨ a ⟩ ]t
  Πη    : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Γ (Π A ([p⁺][⟨q⟩]T {A = B} i))) t (lam (app (t [ p ]Π) q'))
  lam[] : PathP (λ i → Tm Γ (Π[] {B = B}{γ = γ} i)) (lam b [ γ ]t) (lam (b [ γ ⁺ ]t))
  app[] : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Γ ([⟨⟩][]T {A = B}{a = a}{γ = γ} i)) (app t a [ γ ]t') (app (t [ γ ]Π) (a [ γ ]t'))

_[_]t' = _[_]t
q'     = q
_[_]U' = _[_]U

_[_]T* : Ty Γ → Sub Δ Γ → Ty Δ
_[_]T= : (A : Ty Γ)(γ : Sub Δ Γ) → A [ γ ]T ≡ A [ γ ]T*
_[_]t* : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T*)
_[_]t= : (a : Tm Γ A)(γ : Sub Δ Γ) → PathP (λ i → Tm Δ ((A [ γ ]T=) i)) (a [ γ ]t) (a [ γ ]t*)
_∘*_   : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
_∘=_   : (γ : Sub Δ Γ)(δ : Sub Θ Δ) → γ ∘ δ ≡ γ ∘* δ

_⁺*    : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T*) (Γ ▹ A)
_⁺* {Δ = Δ}{Γ = Γ}{A = A} γ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) (A [ γ ]T=) (γ ⁺)

TySet A A' e e' i i' [ γ ]T* = TySet (A [ γ ]T*) (A' [ γ ]T*) (λ i → e i [ γ ]T*) (λ i → e' i [ γ ]T*) i i'
(A [ γ ]T) [ δ ]T* = A [ γ ∘* δ ]T
_[_]T* {Γ} {Δ} ([∘]T {Θ} {A} {Ψ} {θ} {_} {ψ} i) γ = (A [ θ ]T [ ψ ∘* γ ]T=) (~ i) -- [∘]T {Θ} {A} {Ψ} {θ} {_} {ψ} i [ γ ]T
_[_]T* {Γ} {Δ} ([id]T {_} {A} i) γ =  (A [ γ ]T=) i
_[_]T* {Γ} {Δ} ([p][⟨⟩]T {_} {A} {B} {t} i) γ = ([∘]T {Γ ▹ A} {B [ p ]T} {_} {γ ⁺*} {_} {⟨ t [ γ ]t* ⟩} ∙∙ {!cong _[ ⟨ t [ γ ]t* ⟩ ]t*!} ∙∙ {!!}) i -- [p][⁺]T
_[_]T* {_} {Δ} ([p][⁺]T {Θ} {A} {B} {Γ} {θ} i) γ = ([∘]T ∙∙ cong _[ γ ]T ([p][⁺]T {Θ} {A} {B} {Γ} {θ}) ∙∙ sym [∘]T) i
[p⁺][⟨q⟩]T i [ γ ]T* = {!!}
[⟨⟩][]T i [ γ ]T* = {!!}
U [ γ ]T* = U
_[_]T* {Γ} {Δ} (U[] {_} {Θ} {γ₁} i) γ = {!sym ((U[] {Γ} {Θ} {γ₁} i) [ γ ]T=) i!}
El Â [ γ ]T* = El (Â [ γ ]t*)
El[] i [ γ ]T* = {!!}
Π A B [ γ ]T* = Π (A [ γ ]T*) (B [ γ ⁺* ]T*)
Π[] i [ γ ]T* = {!!}

A [ γ ]T= = {!!}

SubSet γ γ₁ x y i j ∘* δ = {!!}
γ ∘ δ ∘* θ = γ ∘* (δ ∘* θ)
ass {γ = γ} {δ = δ} {θ = θ} i ∘* Ξ = γ ∘* (δ ∘* (θ ∘* Ξ))
id ∘* δ = δ
idl {Γ} {Δ} {γ} i ∘* δ = γ ∘* δ
idr {Γ} {Δ} {γ} i ∘* δ = γ ∘* δ
ε ∘* δ = ε
◇η {σ = σ} i ∘* δ = ◇η {σ = σ ∘* δ} i
p ∘* δ = p ∘ δ
γ ⁺ ∘* δ = γ ⁺ ∘ δ
⟨ a ⟩ ∘* γ = γ ⁺* ∘ ⟨ a [ γ ]t* ⟩
∘⁺ i ∘* δ = {!!}
id⁺ i ∘* δ = {!!}
p∘⁺ i ∘* δ = {!!}
p∘⟨⟩ i ∘* δ = {!!}
⟨⟩∘ i ∘* δ = {!!}
p⁺∘⟨q⟩ i ∘* δ = {!!}

_∘=_ = {!!}

a [ γ ]t* = {!!}

a [ γ ]t= = {!!}
