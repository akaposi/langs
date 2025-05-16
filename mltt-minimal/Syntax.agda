{-# OPTIONS --cubical #-}

module mltt-minimal.Syntax where

open import Cubical.Foundations.Prelude hiding (Sub)

infixl 5 _▹_
infixl 8 _∘_
infixl 9 _[_]T _[_]t _[_]U _[_]Π
infixl 10 _⁺
infixl 11 ⟨_⟩

-- Szumi's method

data Sort : Type
data EL : Sort → Type

Con : Type
Sub : Con → Con → Type
Ty : Con → Type
Tm : (Γ : Con) → Ty Γ → Type

data Sort where
  con : Sort
  sub : (Δ Γ : Con) → Sort
  ty : (Γ : Con) → Sort
  tm : (Γ : Con)(A : Ty Γ) → Sort

Con = EL con
Sub Δ Γ = EL (sub Δ Γ)
Ty Γ = EL (ty Γ)
Tm Γ A = EL (tm Γ A)

{-# DISPLAY EL con = Con #-}
{-# DISPLAY EL (sub Δ Γ) = Sub Δ Γ #-}
{-# DISPLAY EL (ty Γ) = Ty Γ #-}
{-# DISPLAY EL (tm Γ A) = Tm Γ A #-}

private variable
  Γ Δ Θ : Con
  γ δ θ σ : Sub Δ Γ
  A B : Ty Γ
  a b Â t : Tm Γ A

data EL where
  SubSet : isSet (Sub Δ Γ)
  TySet  : isSet (Ty Γ)
  TmSet  : isSet (Tm Γ A)

  -- Con
  _▹_ : (Γ : Con)(A : Ty Γ) → Con
  ◇   : Con

  -- Sub
  _∘_    : (γ : Sub Δ Γ)(δ : Sub Θ Δ) → Sub Θ Γ
  ass    : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
  id     : Sub Γ Γ
  idl    : id ∘ γ ≡ γ
  idr    : γ ∘ id ≡ γ
  ε      : Sub Γ ◇
  ◇η     : σ ≡ ε
  p      : Sub (Γ ▹ A) Γ
  ⟨_⟩    : (t : Tm Γ A) → Sub Γ (Γ ▹ A)
  p∘⟨⟩   : p ∘ ⟨ a ⟩ ≡ id

    -- Ty
  _[_]T    : (A : Ty Γ)(γ : Sub Δ Γ) → Ty Δ
  [∘]T     : A [ γ ∘ δ ]T ≡ A [ γ ]T [ δ ]T
  [id]T    : A [ id ]T ≡ A
  [p][⟨⟩]T : {A : Ty Γ}{b : Tm Γ B} → A [ p ]T [ ⟨ b ⟩ ]T ≡ A
  -- [p][⁺]T needs _⁺
  -- [p⁺][⟨q⟩]T and [⟨⟩][]T rules are lower, q and _[_]t are needed for these.
  U        : Ty Γ
  U[]      : U [ γ ]T ≡ U
  El       : (Â : Tm Γ U) → Ty Γ
  -- El[] is below Tm stuff
  Π        : (A : Ty Γ)(B : Ty (Γ ▹ A)) → Ty Γ
  -- Π[] needs _⁺

  -- Tm
  _[_]t : (t : Tm Γ A)(γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
  q     : Tm (Γ ▹ A) (A [ p ]T)
  q[⟨⟩] : PathP (λ i → Tm Γ ([p][⟨⟩]T {A = A}{b = a} i)) (q [ ⟨ a ⟩ ]t) a
  [∘]t  : PathP (λ i → Tm Θ ([∘]T {A = A}{γ = γ}{δ = δ} i)) (a [ γ ∘ δ ]t) (a [ γ ]t [ δ ]t)
  [id]t : PathP (λ i → Tm Γ ([id]T {A = A} i)) (a [ id ]t) a

  _[_]U : (u : Tm Γ U)(γ : Sub Δ Γ) → Tm Δ U
  []U   : PathP (λ i → Tm Δ (U[] {γ = γ} i)) (Â [ γ ]t) (Â [ γ ]U)

  -- Sub again
  _⁺     : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
  ∘⁺     : PathP (λ i → Sub (Θ ▹ [∘]T {A = A}{γ = γ}{δ = δ} i) (Γ ▹ A)) ((γ ∘ δ) ⁺) (γ ⁺ ∘ δ ⁺)
  id⁺    : PathP (λ i → Sub (Γ ▹ [id]T {A = A} i) (Γ ▹ A)) (id ⁺) id
  p∘⁺    : p {A = A} ∘ γ ⁺ ≡ γ ∘ p
  ⟨⟩∘    : ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]t ⟩
  p⁺∘⟨q⟩ : p ⁺ ∘ ⟨ q ⟩ ≡ id {Γ ▹ A}

    -- Ty again
  [p][⁺]T    : A [ p {A = B} ]T [ γ ⁺ ]T ≡ A [ γ ]T [ p ]T
  [p⁺][⟨q⟩]T : A [ p ⁺ ]T [ ⟨ q ⟩ ]T ≡ A
  [⟨⟩][]T    : A [ ⟨ a ⟩ ]T [ γ ]T ≡ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
  El[]       : El Â [ γ ]T ≡ El (Â [ γ ]U)
  Π[]        : Π A B [ γ ]T ≡ Π (A [ γ ]T) (B [ γ ⁺ ]T)

  -- Tm again
  q[⁺]  : PathP (λ i → Tm (Δ ▹ A [ γ ]T) ([p][⁺]T {A = A} i)) (q [ γ ⁺ ]t) q

  _[_]Π : (f : Tm Γ (Π A B))(γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
  lam   : (t : Tm (Γ ▹ A) B) → Tm Γ (Π A B)
  app   : (f : Tm Γ (Π A B))(a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
  Πβ    : app (lam b) a ≡ b [ ⟨ a ⟩ ]t
  Πη    : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Γ (Π A ([p⁺][⟨q⟩]T {A = B} i))) (lam (app (t [ p ]Π) q)) t
  lam[] : PathP (λ i → Tm Γ (Π[] {B = B}{γ = γ} i)) (lam b [ γ ]t) (lam (b [ γ ⁺ ]t))
  app[] : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Δ ([⟨⟩][]T {A = B}{a = a}{γ = γ} i)) (app t a [ γ ]t) (app (t [ γ ]Π) (a [ γ ]t))
