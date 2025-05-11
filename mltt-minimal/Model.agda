{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

module mltt-minimal.Model where

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)

import mltt-minimal.Syntax as I

record Sorts {ℓ}{ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  -- infixl 4 _▹_
  -- infixl 8 _∘_
  -- infixl 10 _⁺
  -- infixl 8 _∘_
  -- infixl 6 _[_]T _[_]t 
  -- infixl 4 _,[_]_ _▹_
  -- infixl 5 _▹_
  field
    Con : Type ℓ
    Sub : Con → Con → Type ℓ'
    Ty  : Con → Type ℓ
    Tm  : (Γ : Con) → Ty Γ → Type ℓ'
   
record Cwf {ℓ}{ℓ'}(sorts : Sorts {ℓ}{ℓ'}) : Type (ℓ ⊔ ℓ') where
  open Sorts sorts
  infixl 10 _⁺
  infixl 8 _∘_
  infixl 9 _[_]T _[_]t
  infixl 5 _▹_
  infixl 11 ⟨_⟩
  field
      SubSet : ∀ {Δ Γ} → isSet (Sub Δ Γ)
      _∘_    : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      ass    : ∀ {Γ Δ Θ Ξ} (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
      id     : ∀ {Γ} → Sub Γ Γ
      idl    : ∀ {Γ Δ} (γ : Sub Δ Γ) → id ∘ γ ≡ γ
      idr    : ∀ {Γ Δ} (γ : Sub Δ Γ) → γ ∘ id ≡ γ

      ◇   : Con
      ε      : ∀ {Γ} → Sub Γ ◇
      ◇η    : ∀ {Γ}{σ : Sub Γ ◇} → σ ≡ ε
        
      TySet      : ∀ {Γ} → isSet (Ty Γ)
      _[_]T      : ∀ {Γ Δ} → Ty Γ → Sub Δ Γ → Ty Δ
      [∘]T       : ∀ {Γ}{A : Ty Γ}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} → A [ γ ∘ δ ]T ≡ A [ γ ]T [ δ ]T
      [id]T      : ∀ {Γ}{A : Ty Γ} → A [ id ]T ≡ A
  
      TmSet : ∀ {Γ}{A : Ty Γ} → isSet (Tm Γ A)
      _[_]t : ∀ {Γ Δ}{A : Ty Γ} → Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
      [∘]t  : ∀{Γ}{A : Ty Γ}{a : Tm Γ A}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} →  PathP (λ i → Tm Θ ([∘]T {Γ}{A}{Δ}{γ}{Θ}{δ} i)) (a [ γ ∘ δ ]t) (a [ γ ]t [ δ ]t) 
      [id]t : ∀ {Γ}{A : Ty Γ}{a : Tm Γ A} → PathP (λ i → Tm Γ ([id]T {A = A} i)) (a [ id ]t) a

      _▹_ : (Γ : Con) → Ty Γ → Con
      p      : ∀ {Γ}{A : Ty Γ} → Sub (Γ ▹ A) Γ
      q     : ∀ {Γ}{A : Ty Γ} → Tm (Γ ▹ A) (A [ p ]T)
      _⁺     : ∀ {Δ Γ}{A : Ty Γ}(γ : Sub Δ Γ) → Sub ((Δ ▹ (A [ γ ]T))) (Γ ▹ A)
      ⟨_⟩    : ∀ {Γ}{A : Ty Γ} → Tm Γ A → Sub Γ (Γ ▹ A)
      [p][⟨⟩]T   : ∀ {Γ}{A B : Ty Γ}{b : Tm Γ B} → (A [ p ]T [ ⟨ b ⟩ ]T) ≡ A 
      [p][⁺]T    : ∀ {Γ Δ : Con}{γ : Sub Δ Γ}{A B : Ty Γ} → A [ p {A = B} ]T [ γ ⁺ ]T ≡ A [ γ ]T [ p ]T 
      [p⁺][⟨q⟩]T : ∀ {Γ }{A : Ty Γ}{B : Ty (Γ ▹ A)} → B ≡ B [ p {Γ}{A} ⁺ ]T [ ⟨ q ⟩ ]T
      [⟨⟩][]T    : ∀ {Γ Δ : Con}{γ : Sub Δ Γ}{A' : Ty Γ}{A : Ty (Γ ▹ A')}{a : Tm Γ A'} → (A [ ⟨ a ⟩ ]T [ γ ]T) ≡ (A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T) 
      ∘⁺     : ∀ {Γ Δ Θ}{A : Ty Γ}{γ : Sub Δ Γ}{δ : Sub Θ Δ} → PathP (λ i → Sub (Θ ▹ [∘]T {A = A}{γ = γ}{δ = δ} i) (Γ ▹ A)) ((γ ∘ δ) ⁺) (γ ⁺ ∘ δ ⁺) 
      id⁺    : ∀ {Γ}{A : Ty Γ} → PathP (λ i → Sub (Γ ▹ [id]T {A = A} i) (Γ ▹ A)) (id ⁺) id
      p∘⁺    : ∀ {Γ Δ}{γ : Sub Δ Γ}{A : Ty Γ}{a : Tm Γ A} → p {A = A} ∘ γ ⁺ ≡ γ ∘ p
      p∘⟨⟩   : ∀ {Γ}{A : Ty Γ}{a : Tm Γ A} → p ∘ ⟨ a ⟩ ≡ id
      ⟨⟩∘    : ∀ {Γ Δ}{γ : Sub Δ Γ}{A : Ty Γ}{a : Tm Γ A} → ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]t ⟩
      p⁺∘⟨q⟩ : ∀ {Γ}{A : Ty Γ} → id {Γ ▹ A} ≡ p ⁺ ∘ ⟨ q ⟩
      q[⟨⟩] : ∀ {Γ}{A : Ty Γ}{a : Tm Γ A} → PathP (λ i → Tm Γ ([p][⟨⟩]T {A = A}{b = a} i)) (q [ ⟨ a ⟩ ]t) a
      q[⁺]  : ∀ {Γ Δ}{A : Ty Γ}{γ : Sub Δ Γ} → PathP (λ i → Tm (Δ ▹ A [ γ ]T) ([p][⁺]T {A = A} i)) (q [ γ ⁺ ]t) q

record TF {ℓ}{ℓ'}(sorts : Sorts {ℓ}{ℓ'})(cwf : Cwf {ℓ}{ℓ'}(sorts)) : Type (ℓ ⊔ ℓ') where
  open Sorts sorts
  open Cwf cwf
  infixl 9 _[_]Π _[_]U
  field
      U        : ∀ {Γ} → Ty Γ
      U[]      : ∀ {Γ Δ}{γ : Sub Δ Γ} → (U [ γ ]T) ≡ U
      _[_]U : ∀ {Γ Δ} → Tm Γ U → (γ : Sub Δ Γ) → Tm Δ U
      []U   : ∀ {Δ α}{γ : Sub Δ α}{Â : Tm α U} → PathP (λ i → Tm Δ (U[] {γ = γ} i)) (Â [ γ ]t) (Â [ γ ]U)
    
      El       : ∀ {Γ} → Tm Γ U → Ty Γ
      El[]     : ∀ {Γ Δ}{γ : Sub Δ Γ}{Â : Tm Γ U} → El Â [ γ ]T ≡ El (Â [ γ ]U)
    
      Π        : ∀ {Γ} → (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
      Π[]      : ∀ {Γ Δ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{γ : Sub Δ Γ} → Π {Γ} A B [ γ ]T ≡ Π (A [ γ ]T) (B [ γ ⁺ ]T)
      _[_]Π : ∀ {Γ Δ}{A : Ty Γ}{B : Ty (Γ ▹ A)} → Tm Γ (Π A B) → (γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
      lam   : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)} → Tm (Γ ▹ A) B → Tm Γ (Π A B)
      app   : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)} → Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
      Πβ    : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{b : Tm (Γ ▹ A) B} → (a : Tm Γ A) → app (lam b) a ≡ b [ ⟨ a ⟩ ]t
      Πη    : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{t : Tm Γ (Π A B)} →  PathP (λ i → Tm Γ (Π A ([p⁺][⟨q⟩]T {A = A}{B = B} i))) t (lam (app (t [ p ]Π) q))
      lam[] : ∀ {Γ Δ}{A : Ty Δ}{B : Ty (Δ ▹ A)}{γ : Sub Γ Δ}{b : Tm (Δ ▹ A) B}  → PathP (λ i → Tm Γ (Π[] {B = B}{γ = γ} i)) (lam b [ γ ]t) (lam (b [ γ ⁺ ]t))
      app[] : ∀ {Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{a : Tm Γ A}{γ : Sub Γ Γ}{t : Tm Γ (Π A B)} →  PathP (λ i → Tm Γ ([⟨⟩][]T {γ = γ}{A = B}{a = a} i)) (app t a [ γ ]t) (app (t [ γ ]Π) (a [ γ ]t))
