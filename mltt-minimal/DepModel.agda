{-# OPTIONS --cubical --guardedness #-}

module mltt-minimal.DepModel where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)

open import Agda.Primitive
open import mltt-minimal.Syntax

private variable
  Γ Δ Θ Ξ : Con
  γ δ θ σ : Sub Δ Γ
  A B : Ty Γ
  a b Â t : Tm Γ A
  u : Tm Γ U

record DepModel {ℓ₁ ℓ₂ ℓ₃ ℓ₄} : Type (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  infixl 5 _▹∙_
  infixl 8 _∘∙_
  infixl 9 _[_]T∙ _[_]t∙ _[_]U∙ _[_]Π∙
  infixl 10 _⁺∙
  infixl 11 ⟨_⟩∙
  infixl 20 ⟦_⟧L {- Dubious cheating, it is fine in this case. Don't use Level with Setω. -} ⟦_⟧Sort ⟦_⟧
  field
    Con∙ : Con → Type ℓ₁
    Sub∙ : {Δ Γ : Con}(Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → Type ℓ₂ -- (ℓ₁ ⊔ ℓ₂)
    Ty∙  : {Γ : Con}(Γ∙ : Con∙ Γ)(A : Ty Γ) → Type ℓ₃ -- (ℓ₁ ⊔ ℓ₃)
    Tm∙  : {Γ : Con}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A)(t : Tm Γ A) → Type ℓ₄ -- (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄)

    _▹∙_ : (Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A) → Con∙ (Γ ▹ A)
    ◇∙   : Con∙ ◇

    SubSet∙ : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ} → isSet (Sub∙ Δ∙ Γ∙ γ)
    TySet∙  : {Γ∙ : Con∙ Γ} → isSet (Ty∙ Γ∙ A)
    TmSet∙  : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → isSet (Tm∙ Γ∙ A∙ a)

    -- Sub
    _∘∙_    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Θ∙ : Con∙ Θ}(γ∙ : Sub∙ Δ∙ Γ∙ γ)(δ∙ : Sub∙ Θ∙ Δ∙ δ) → Sub∙ Θ∙ Γ∙ (γ ∘ δ)
    ass∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Θ∙ : Con∙ Θ}{Ξ∙ : Con∙ Ξ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}{θ∙ : Sub∙ Ξ∙ Θ∙ θ} → PathP (λ i → Sub∙ Ξ∙ Γ∙ (ass {γ = γ} {δ = δ} {θ = θ} i)) ((γ∙ ∘∙ δ∙) ∘∙ θ∙) (γ∙ ∘∙ (δ∙ ∘∙ θ∙))
    id∙     : {Γ∙ : Con∙ Γ} → Sub∙ Γ∙ Γ∙ id
    idl∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Sub∙ Δ∙ Γ∙ (idl {γ = γ} i)) (id∙ ∘∙ γ∙) γ∙
    idr∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Sub∙ Δ∙ Γ∙ (idr {γ = γ} i)) (γ∙ ∘∙ id∙) γ∙
    ε∙      : {Γ∙ : Con∙ Γ} → Sub∙ Γ∙ ◇∙ ε
    ◇η∙     : {Γ∙ : Con∙ Γ}{σ∙ : Sub∙ Γ∙ ◇∙ σ} → PathP (λ i → Sub∙ Γ∙ ◇∙ (◇η {σ = σ} i)) σ∙ ε∙
    p∙      : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
    ⟨_⟩∙    : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}(t∙ : Tm∙ Γ∙ A∙ t) → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ t ⟩
    p∘⟨⟩∙   : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a} → PathP (λ i → Sub∙ Γ∙ Γ∙ (p∘⟨⟩ {a = a} i)) (p∙ ∘∙ ⟨ a∙ ⟩∙) id∙

    -- Ty
    _[_]T∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Ty∙ Δ∙ (A [ γ ]T)
    [∘]T∙     : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Θ∙ : Con∙ Θ}{A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ} → PathP (λ i → Ty∙ Θ∙ ([∘]T {A = A} {γ = γ} {δ = δ} i)) (A∙ [ γ∙ ∘∙ δ∙ ]T∙) (A∙ [ γ∙ ]T∙ [ δ∙ ]T∙)
    [id]T∙    : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → PathP (λ i → Ty∙ Γ∙ ([id]T {A = A} i)) (A∙ [ id∙ ]T∙) A∙
    [p][⟨⟩]T∙ : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ Γ∙ B}{b∙ : Tm∙ Γ∙ B∙ b} → PathP (λ i → Ty∙ Γ∙ ([p][⟨⟩]T {A = A} {b = b} i)) (A∙ [ p∙ ]T∙ [ ⟨ b∙ ⟩∙ ]T∙) A∙
    -- [p][⁺]T∙ needs _⁺∙
    -- [p⁺][⟨q⟩]T and [⟨⟩][]T rules are lower, q and _[_]t are needed for these.
    U∙        : {Γ∙ : Con∙ Γ} → Ty∙ Γ∙ U
    U[]∙      : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Ty∙ Δ∙ (U[] {γ = γ} i)) (U∙ [ γ∙ ]T∙) U∙
    El∙       : {Γ∙ : Con∙ Γ}(Â∙ : Tm∙ Γ∙ U∙ Â) → Ty∙ Γ∙ (El Â)
    -- El[]∙ is below Tm stuff
    Π∙        : {Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Π A B)
    -- Π[]∙ needs _⁺∙

    -- Tm
    _[_]t∙ : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}(a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
    q∙     : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ ]T∙) q
    q[⟨⟩]∙ : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a} → PathP (λ i → Tm∙ Γ∙ ([p][⟨⟩]T∙ {A∙ = A∙}{b∙ = a∙} i) (q[⟨⟩] i)) (q∙ [ ⟨ a∙ ⟩∙ ]t∙) a∙
    [∘]t∙  : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Θ∙ : Con∙ Θ}{A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}{a∙ : Tm∙ Γ∙ A∙ a} → PathP (λ i → Tm∙ Θ∙ ([∘]T∙ {A∙ = A∙}{γ∙ = γ∙}{δ∙ = δ∙} i) ([∘]t {a = a} i)) (a∙ [ γ∙ ∘∙ δ∙ ]t∙) (a∙ [ γ∙ ]t∙ [ δ∙ ]t∙)
    [id]t∙ : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a} → PathP (λ i → Tm∙ Γ∙ ([id]T∙ {A∙ = A∙} i) ([id]t {a = a} i)) (a∙ [ id∙ ]t∙) a∙

    _[_]U∙ : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}(u∙ : Tm∙ Γ∙ U∙ u)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ U∙ (u [ γ ]U)
    []U∙   : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{Â∙ : Tm∙ Γ∙ U∙ Â} → PathP (λ i → Tm∙ Δ∙ (U[]∙ {γ∙ = γ∙} i) ([]U {Â = Â} i)) (Â∙ [ γ∙ ]t∙) (Â∙ [ γ∙ ]U∙)

    -- Sub again
    _⁺∙     : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) (Γ∙ ▹∙ A∙) (γ ⁺)
    ∘⁺∙     : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Θ∙ : Con∙ Θ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Δ∙ δ}{A∙ : Ty∙ Γ∙ A} → PathP (λ i → Sub∙ (Θ∙ ▹∙ [∘]T∙ {A∙ = A∙}{γ∙ = γ∙}{δ∙ = δ∙} i) (Γ∙ ▹∙ A∙) (∘⁺ i)) ((γ∙ ∘∙ δ∙) ⁺∙) (γ∙ ⁺∙ ∘∙ δ∙ ⁺∙)
    id⁺∙    : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → PathP (λ i → Sub∙ (Γ∙ ▹∙ [id]T∙ {A∙ = A∙} i) (Γ∙ ▹∙ A∙) (id⁺ i)) (id∙ ⁺∙) id∙
    p∘⁺∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{A∙ : Ty∙ Γ∙ A} → PathP (λ i → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) Γ∙ (p∘⁺ i)) (p∙ ∘∙ γ∙ ⁺∙) (γ∙ ∘∙ p∙)
    ⟨⟩∘∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Sub∙ Δ∙ (Γ∙ ▹∙ A∙) (⟨⟩∘ {a = a}{γ = γ} i)) (⟨ a∙ ⟩∙ ∘∙ γ∙) (γ∙ ⁺∙ ∘∙ ⟨ a∙ [ γ∙ ]t∙ ⟩∙)
    p⁺∘⟨q⟩∙ : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A} → PathP (λ i → Sub∙ (Γ∙ ▹∙ A∙) (Γ∙ ▹∙ A∙) (p⁺∘⟨q⟩ i)) (p∙ ⁺∙ ∘∙ ⟨ q∙ ⟩∙) id∙

    -- Ty again
    [p][⁺]T∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ Γ∙ B}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Ty∙ (Δ∙ ▹∙ B∙ [ γ∙ ]T∙) ([p][⁺]T {A = A} {B = B} i)) (A∙ [ p∙ ]T∙ [ γ∙ ⁺∙ ]T∙) (A∙ [ γ∙ ]T∙ [ p∙ ]T∙)
    [p⁺][⟨q⟩]T∙ : {Γ∙ : Con∙ Γ}{B∙ : Ty∙ Γ∙ B}{A∙ : Ty∙ (Γ∙ ▹∙ B∙) A} → PathP (λ i → Ty∙ (Γ∙ ▹∙ B∙) ([p⁺][⟨q⟩]T {A = A} i)) (A∙ [ p∙ ⁺∙ ]T∙ [ ⟨ q∙ ⟩∙ ]T∙) A∙
    [⟨⟩][]T∙    : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{B∙ : Ty∙ Γ∙ B}{A∙ : Ty∙ (Γ∙ ▹∙ B∙) A}{a∙ : Tm∙ Γ∙ B∙ a}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Ty∙ Δ∙ ([⟨⟩][]T {A = A} {a = a} {γ = γ} i)) (A∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙) (A∙ [ γ∙ ⁺∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙)
    El[]∙       : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{Â∙ : Tm∙ Γ∙ U∙ Â}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Ty∙ Δ∙ (El[] {Â = Â} {γ = γ} i)) (El∙ Â∙ [ γ∙ ]T∙) (El∙ (Â∙ [ γ∙ ]U∙))
    Π[]∙        : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Ty∙ Δ∙ (Π[] {A = A}{B = B}{γ = γ} i)) (Π∙ A∙ B∙ [ γ∙ ]T∙) (Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙))

    -- Tm again
    q[⁺]∙  : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → PathP (λ i → Tm∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) ([p][⁺]T∙ {A∙ = A∙} i) (q[⁺] i)) (q∙ [ γ∙ ⁺∙ ]t∙) q∙

    _[_]Π∙ : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{f : Tm Γ (Π A B)}(f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)) (f [ γ ]Π)
    []Π∙   : {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{t∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) t} → PathP (λ i → Tm∙ Δ∙ (Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} i) ([]Π {A = A} {B = B} {γ = γ} {t = t} i)) (t∙ [ γ∙ ]t∙) (t∙ [ γ∙ ]Π∙)
    lam∙   : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}(t∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ t) → Tm∙ Γ∙ (Π∙ A∙ B∙) (lam t)
    app∙   : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}(t∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) t)(a∙ : Tm∙ Γ∙ A∙ a) → Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) (app t a)
    Πβ∙    : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b}{a∙ : Tm∙ Γ∙ A∙ a} → PathP (λ i → Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) (Πβ {b = b} i)) (app∙ (lam∙ b∙) a∙) (b∙ [ ⟨ a∙ ⟩∙ ]t∙)
    Πη∙    : {Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{t∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) t} → PathP (λ i → Tm∙ Γ∙ (Π∙ A∙ ([p⁺][⟨q⟩]T∙ {A∙ = B∙} i)) (Πη {t = t} i)) (lam∙ (app∙ (t∙ [ p∙ ]Π∙) q∙)) t∙
    lam[]∙ : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b} → PathP (λ i → Tm∙ Δ∙ (Π[]∙ {B∙ = B∙}{γ∙ = γ∙} i) (lam[] {b = b} i)) (lam∙ b∙ [ γ∙ ]t∙) (lam∙ (b∙ [ γ∙ ⁺∙ ]t∙))
    app[]∙ : {Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a∙ : Tm∙ Γ∙ A∙ a}{γ∙ : Sub∙ Δ∙ Γ∙ γ}{t∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) t} → PathP (λ i → Tm∙ Δ∙ ([⟨⟩][]T∙ {A∙ = B∙}{a∙ = a∙}{γ∙ = γ∙} i) (app[] {t = t} i)) (app∙ t∙ a∙ [ γ∙ ]t∙) (app∙ (t∙ [ γ∙ ]Π∙) (a∙ [ γ∙ ]t∙))

  ⟦_⟧L : (S : Sort) → Level
  ⟦ con ⟧L = ℓ₁
  ⟦ sub _ _ ⟧L = ℓ₂
  ⟦ ty _ ⟧L = ℓ₃
  ⟦ tm _ _ ⟧L = ℓ₄

  ⟦_⟧Sort : (S : Sort) → EL S → Type ⟦ S ⟧L
  ⟦_⟧ : {S : Sort}(s : EL S) → ⟦ S ⟧Sort s

  ⟦ con ⟧Sort = Con∙
  ⟦ sub Δ Γ ⟧Sort = Sub∙ ⟦ Δ ⟧ ⟦ Γ ⟧
  ⟦ ty Γ ⟧Sort = Ty∙ ⟦ Γ ⟧
  ⟦ tm Γ A ⟧Sort = Tm∙ ⟦ Γ ⟧ ⟦ A ⟧

  ⟦ SubSet γ δ e1 e2 i j ⟧ = isOfHLevel→isOfHLevelDep 2 (λ γ' → SubSet∙ {γ = γ'}) ⟦ γ ⟧ ⟦ δ ⟧ (cong ⟦_⟧ e1) (cong ⟦_⟧ e2) (SubSet γ δ e1 e2) i j
  ⟦ TySet A B e1 e2 i j ⟧ = isOfHLevel→isOfHLevelDep 2 (λ A' → TySet∙ {A = A'}) ⟦ A ⟧ ⟦ B ⟧ (cong ⟦_⟧ e1) (cong ⟦_⟧ e2) (TySet A B e1 e2) i j
  ⟦ TmSet t1 t2 e1 e2 i j ⟧ = isOfHLevel→isOfHLevelDep 2 (λ t' → TmSet∙ {a = t'}) ⟦ t1 ⟧ ⟦ t2 ⟧ (cong ⟦_⟧ e1) (cong ⟦_⟧ e2) (TmSet t1 t2 e1 e2) i j
  ⟦ Γ ▹ A ⟧ =  ⟦ Γ ⟧ ▹∙ ⟦ A ⟧
  ⟦ ◇ ⟧ = ◇∙
  ⟦ γ ∘ δ ⟧ = ⟦ γ ⟧ ∘∙ ⟦ δ ⟧
  ⟦ ass {γ = γ} {δ = δ} {θ = θ} i ⟧ = ass∙ {γ∙ = ⟦ γ ⟧} {δ∙ = ⟦ δ ⟧} {θ∙ = ⟦ θ ⟧} i
  ⟦ id ⟧ = id∙
  ⟦ idl {γ = γ} i ⟧ = idl∙ {γ∙ = ⟦ γ ⟧} i
  ⟦ idr {γ = γ} i ⟧ = idr∙ {γ∙ = ⟦ γ ⟧} i
  ⟦ ε ⟧ = ε∙
  ⟦ ◇η {σ = σ} i ⟧ = ◇η∙ {σ∙ = ⟦ σ ⟧} i
  ⟦ p ⟧ = p∙
  ⟦ ⟨ t ⟩ ⟧ = ⟨ ⟦ t ⟧ ⟩∙
  ⟦ p∘⟨⟩ {a = a} i ⟧ = p∘⟨⟩∙ {a∙ = ⟦ a ⟧} i
  ⟦ A [ γ ]T ⟧ = ⟦ A ⟧ [ ⟦ γ ⟧ ]T∙
  ⟦ [∘]T {A = A} {γ = γ} {δ = δ} i ⟧ = [∘]T∙ {A∙ = ⟦ A ⟧} {γ∙ = ⟦ γ ⟧} {δ∙ = ⟦ δ ⟧} i
  ⟦ [id]T {A = A} i ⟧ = [id]T∙ {A∙ = ⟦ A ⟧} i
  ⟦ [p][⟨⟩]T {A = A} {b = b} i ⟧ = [p][⟨⟩]T∙ {A∙ = ⟦ A ⟧} {b∙ = ⟦ b ⟧} i
  ⟦ U ⟧ = U∙
  ⟦ U[] {γ = γ} i ⟧ = U[]∙ {γ∙ = ⟦ γ ⟧} i
  ⟦ El Â ⟧ = El∙ ⟦ Â ⟧
  ⟦ Π A B ⟧ = Π∙ ⟦ A ⟧ ⟦ B ⟧
  ⟦ t [ γ ]t ⟧ = ⟦ t ⟧ [ ⟦ γ ⟧ ]t∙
  ⟦ q ⟧ = q∙
  ⟦ q[⟨⟩] {a = a} i ⟧ = q[⟨⟩]∙ {a∙ = ⟦ a ⟧} i
  ⟦ [∘]t {γ = γ} {δ = δ} {a = a} i ⟧ = [∘]t∙ {γ∙ = ⟦ γ ⟧} {δ∙ = ⟦ δ ⟧} {a∙ = ⟦ a ⟧} i
  ⟦ [id]t {a = a} i ⟧ = [id]t∙ {a∙ = ⟦ a ⟧} i
  ⟦ u [ γ ]U ⟧ = ⟦ u ⟧ [ ⟦ γ ⟧ ]U∙
  ⟦ []U {γ = γ} {Â = Â} i ⟧ = []U∙ {γ∙ = ⟦ γ ⟧} {Â∙ = ⟦ Â ⟧} i
  ⟦ γ ⁺ ⟧ = ⟦ γ ⟧ ⁺∙
  ⟦ ∘⁺ {γ = γ} {δ = δ} i ⟧ = ∘⁺∙ {γ∙ = ⟦ γ ⟧} {δ∙ = ⟦ δ ⟧} i
  ⟦ id⁺ i ⟧ = id⁺∙ i
  ⟦ p∘⁺ {γ = γ} i ⟧ = p∘⁺∙ {γ∙ = ⟦ γ ⟧} i
  ⟦ ⟨⟩∘ {a = a} {γ = γ} i ⟧ = ⟨⟩∘∙ {a∙ = ⟦ a ⟧} {γ∙ = ⟦ γ ⟧} i
  ⟦ p⁺∘⟨q⟩ i ⟧ = p⁺∘⟨q⟩∙ i
  ⟦ [p][⁺]T {A = A} {γ = γ} i ⟧ = [p][⁺]T∙ {A∙ = ⟦ A ⟧} {γ∙ = ⟦ γ ⟧} i
  ⟦ [p⁺][⟨q⟩]T {A = A} i ⟧ = [p⁺][⟨q⟩]T∙ {A∙ = ⟦ A ⟧} i
  ⟦ [⟨⟩][]T {A = A} {a = a} {γ = γ} i ⟧ = [⟨⟩][]T∙ {A∙ = ⟦ A ⟧} {a∙ = ⟦ a ⟧} {γ∙ = ⟦ γ ⟧} i
  ⟦ El[] {Â = Â} {γ = γ} i ⟧ = El[]∙ {Â∙ = ⟦ Â ⟧} {γ∙ = ⟦ γ ⟧} i
  ⟦ Π[] {A = A} {B = B} {γ = γ} i ⟧ = Π[]∙ {A∙ = ⟦ A ⟧} {B∙ = ⟦ B ⟧} {γ∙ = ⟦ γ ⟧} i
  ⟦ q[⁺] {γ = γ} i ⟧ = q[⁺]∙ {γ∙ = ⟦ γ ⟧} i
  ⟦ f [ γ ]Π ⟧ = ⟦ f ⟧ [ ⟦ γ ⟧ ]Π∙
  ⟦ []Π {Δ = Δ} {Γ} {A} {B} {γ} {t} i ⟧ = []Π∙ {γ∙ = ⟦ γ ⟧} {t∙ = ⟦ t ⟧} i
  ⟦ lam t ⟧ = lam∙ ⟦ t ⟧
  ⟦ app f a ⟧ = app∙ ⟦ f ⟧ ⟦ a ⟧ 
  ⟦ Πβ {b = b} {a = a} i ⟧ = Πβ∙ {b∙ = ⟦ b ⟧} {a∙ = ⟦ a ⟧} i
  ⟦ Πη {t = t} i ⟧ = Πη∙ {t∙ = ⟦ t ⟧} i
  ⟦ lam[] {γ = γ} {b = b} i ⟧ = lam[]∙ {γ∙ = ⟦ γ ⟧} {b∙ = ⟦ b ⟧} i
  ⟦ app[] {a = a} {γ = γ} {t = t} i ⟧ = app[]∙ {a∙ = ⟦ a ⟧} {γ∙ = ⟦ γ ⟧} {t∙ = ⟦ t ⟧} i

open DepModel public
