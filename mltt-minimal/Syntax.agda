{-# OPTIONS --cubical #-}

module mltt-minimal.Syntax where

open import Cubical.Foundations.Prelude hiding (Sub)

infixl 5 _▹_
infixl 8 _∘_ _∘'_
infixl 9 _[_]T _[_]T' _[_]t _[_]t' _[_]U _[_]U' _[_]Π
infixl 10 _⁺ _⁺'
infixl 11 ⟨_⟩ ⟨_⟩'

data Con : Type
data Sub : Con → Con → Type
data Ty  : Con → Type
data Tm  : (Γ : Con) → Ty Γ → Type

private variable
  Γ Δ Θ : Con
  γ δ θ σ : Sub Δ Γ
  A B : Ty Γ
  a b Â t : Tm Γ A

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
