{-# OPTIONS --cubical --no-postfix-projections --guardedness #-}

module mltt-minimal.TakesYearsToLoadSubPi where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import mltt-minimal.Syntax

infixl 9 _[_]Π∙'

_[_]Π∙' : {Δ Γ : Con}{A : Ty Γ}{B : Ty (Γ ▹ A)}{γ : Sub Δ Γ}{Δ∙ Γ∙ : ⊤}
          {A∙ : {Δ : Con}(γ : Sub Δ Γ) → Σ (Ty Δ) (A [ γ ]T ≡_)}{B∙ : {Δ : Con}(γ : Sub Δ (Γ ▹ A)) → Σ (Ty Δ) (B [ γ ]T ≡_)}
          {f : Tm Γ (Π A B)}(f∙ : {Δ : Con}(γ : Sub Δ Γ) → let (A[γ]T , e1) = A∙ γ; (B[γ⁺]T , e2) = B∙ (subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺)) in Σ (Tm Δ (Π A[γ]T B[γ⁺]T)) (PathP (λ i → Tm Δ ((Π[] {A = A} {B = B} {γ = γ} ∙ (λ i₁ → Π (e1 i₁) (toPathP {A = λ i → Ty (Δ ▹ e1 i)} {x = B [ γ ⁺ ]T} (subst-[]T {Γ ▹ A} {Δ ▹ A [ γ ]T} {B} {γ ⁺} {Δ ▹ A[γ]T} {congS (Δ ▹_) e1} ∙ e2) i₁))) i)) (f [ γ ]t)))
          (γ∙ : {Θ : Con}(δ : Sub Θ Δ) → Σ (Sub Θ Γ) (γ ∘ δ ≡_)){Θ : Con}(δ : Sub Θ Δ)
        → let (A[γ]T , e0) = A∙ γ
              (γ∘*δ , e1) = γ∙ δ

              Π[]' : Π (A [ γ ]T) (B [ γ ⁺ ]T) [ δ ]T ≡ Π (A [ γ ]T [ δ ]T) (B [ γ ⁺ ]T [ δ ⁺ ]T)
              Π[]' = Π[] {A = A [ γ ]T} {B = B [ γ ⁺ ]T} {γ = δ}

              [∘]T-simplest = [∘]T {Γ} {A} {Δ} {γ} {Θ} {δ}

              sym[∘]T-simplest = sym [∘]T-simplest

              congA[e1]T : A [ γ ∘ δ ]T ≡ A [ γ∘*δ ]T
              congA[e1]T = congS (A [_]T) e1

              eq0 : A [ γ ]T [ δ ]T ≡ A [ γ∘*δ ]T
              eq0 = sym[∘]T-simplest ∙ congA[e1]T
              
              δ⁺ = subst (λ z → Sub (Θ ▹ z) (Δ ▹ A [ γ ]T)) eq0 (δ ⁺)
              
          in Σ (Tm Θ (Π (A [ γ∘*δ ]T) (B [ γ ⁺ ∘ δ⁺ ]T)))
               (PathP (λ i → Tm Θ ((Π[]' ∙ (λ i₁ → Π (eq0 i₁)
                 (toPathP {A = λ i → Ty (Θ ▹ eq0 i)} {x = B [ γ ⁺ ]T [ δ ⁺ ]T}
                  (subst-[]T {Δ ▹ A [ γ ]T} {Θ ▹ A [ γ ]T [ δ ]T} {B [ γ ⁺ ]T} {δ ⁺} {Θ ▹ A [ γ∘*δ ]T} {congS (Θ ▹_) eq0} ∙
                  (sym ([∘]T {Γ ▹ A} {B} {Δ ▹ A [ γ ]T} {γ ⁺} {Θ ▹ A [ γ∘*δ ]T} {δ⁺})) ∙
                  (λ i₂ → B [ γ ⁺ ∘ δ⁺ ]T)) i₁))) i)) (f [ γ ]Π [ δ ]t))

_[_]Π∙' {Δ} {Γ} {A} {B} {γ} {Δ∙} {Γ∙} {A∙} {B∙} {f} f∙ γ∙ {Θ} δ =
  let
    (γ∘*δ , e1) = γ∙ δ

    Π[]' : Π (A [ γ ]T) (B [ γ ⁺ ]T) [ δ ]T ≡ Π (A [ γ ]T [ δ ]T) (B [ γ ⁺ ]T [ δ ⁺ ]T)
    Π[]' = Π[] {A = A [ γ ]T} {B = B [ γ ⁺ ]T} {γ = δ}

    symΠ[] : Π (A [ γ ]T [ δ ]T) (B [ γ ⁺ ]T [ δ ⁺ ]T) ≡ Π (A [ γ ]T) (B [ γ ⁺ ]T) [ δ ]T
    symΠ[] = sym Π[]'

    [∘]T-simplest : A [ γ ∘ δ ]T ≡ A [ γ ]T [ δ ]T
    [∘]T-simplest = [∘]T {Γ} {A} {Δ} {γ} {Θ} {δ}

    sym[∘]T-simplest : A [ γ ]T [ δ ]T ≡ A [ γ ∘ δ ]T
    sym[∘]T-simplest = sym [∘]T-simplest

    congA[e1]T : A [ γ ∘ δ ]T ≡ A [ γ∘*δ ]T
    congA[e1]T = congS (A [_]T) e1

    eq0 : A [ γ ]T [ δ ]T ≡ A [ γ∘*δ ]T
    eq0 = sym[∘]T-simplest ∙ congA[e1]T
    
    eq1 : Θ ▹ A [ γ ]T [ δ ]T ≡ Θ ▹ A [ γ∘*δ ]T
    eq1 = congS {ℓ-zero} {ℓ-zero} {Ty Θ} {A [ γ ]T [ δ ]T} {A [ γ∘*δ ]T} {Con} (Θ ▹_) eq0

    δ⁺ : Sub (Θ ▹ A [ γ∘*δ ]T) (Δ ▹ A [ γ ]T)
    δ⁺ = subst (λ z → Sub (Θ ▹ z) (Δ ▹ A [ γ ]T)) eq0 (δ ⁺)

    eq2 : γ∘*δ ⁺ ≡ γ ⁺ ∘ δ⁺
    eq2 = fromPathP⁻ {ℓ-zero} {λ i → Sub (Θ ▹ A [ snd (γ∙ δ) (~ i) ]T) (Γ ▹ A)} {γ∘*δ ⁺} {(γ ∘ δ) ⁺} (cong {ℓ-zero} {Sub Θ Γ} {ℓ-zero} {λ z → Sub (Θ ▹ A [ z ]T) (Γ ▹ A)} {γ∘*δ} {γ ∘ δ} _⁺ (sym e1)) ∙ congS {ℓ-zero} {ℓ-zero} {Sub (Θ ▹ A [ γ ∘ δ ]T) (Γ ▹ A)} {(γ ∘ δ) ⁺} {transport⁻ {ℓ-zero} {Sub (Θ ▹ A [ γ ∘ δ ]T) (Γ ▹ A)} {Sub (Θ ▹ A [ γ ]T [ δ ]T) (Γ ▹ A)} (λ i → Sub (Θ ▹ [∘]T-simplest i) (Γ ▹ A)) (γ ⁺ ∘ δ ⁺)} {Sub (Θ ▹ A [ γ∘*δ ]T) (Γ ▹ A)} (transport⁻ {ℓ-zero} {Sub (Θ ▹ A [ γ∘*δ ]T) (Γ ▹ A)} {Sub (Θ ▹ A [ γ ∘ δ ]T) (Γ ▹ A)} (λ i → Sub (Θ ▹ A [ e1 (~ i) ]T) (Γ ▹ A))) (fromPathP⁻ {ℓ-zero} {λ i → Sub (Θ ▹ [∘]T-simplest i) (Γ ▹ A)} {(γ ∘ δ) ⁺} {γ ⁺ ∘ δ ⁺} (∘⁺ {Θ = Θ} {Γ = Γ} {A = A} {γ = γ} {δ = δ})) ∙ sym (substComposite (λ z → Sub z (Γ ▹ A)) (congS (Θ ▹_) sym[∘]T-simplest) (congS {ℓ-zero} {ℓ-zero} {Sub Θ Γ} {γ ∘ δ} {γ∘*δ} {Con} (λ x → Θ ▹ A [ x ]T) e1) (γ ⁺ ∘ δ ⁺)) ∙ sym (congS {ℓ-zero} {ℓ-zero} {Θ ▹ A [ γ ]T [ δ ]T ≡ Θ ▹ A [ γ∘*δ ]T} {congS (Θ ▹_) (sym[∘]T-simplest ∙ (λ i → A [ snd (γ∙ δ) i ]T))} {congS (Θ ▹_) sym[∘]T-simplest ∙ congS (Θ ▹_) (λ i → A [ snd (γ∙ δ) i ]T)} {Sub (Θ ▹ A [ γ∘*δ ]T) (Γ ▹ A)} (λ x → subst (λ z → Sub z (Γ ▹ A)) x (γ ⁺ ∘ δ ⁺)) (cong-∙ (Θ ▹_) sym[∘]T-simplest (congS {ℓ-zero} {ℓ-zero} {Sub Θ Γ} {γ ∘ δ} {γ∘*δ} {Ty Θ} (A [_]T) e1))) ∙ sym (subst-∘ᵣ {γ = γ ⁺} {δ = δ ⁺} {e = eq1})

    e2 : Π (A [ γ ]T) (B [ γ ⁺ ]T) [ δ ]T ≡ Π (A [ γ∘*δ ]T) (B [ γ ⁺ ∘ δ⁺ ]T)
    e2 = Π[]' ∙ (λ i₁ → Π (eq0 i₁)
         (toPathP {A = λ i → Ty (Θ ▹ eq0 i)} {x = B [ γ ⁺ ]T [ δ ⁺ ]T}
            (subst-[]T {A = B [ γ ⁺ ]T} {γ = δ ⁺} {e = eq1}
            ∙ sym ([∘]T {A = B} {γ = γ ⁺} {δ = δ⁺})
            ∙ refl {x = B [ γ ⁺ ∘ δ⁺ ]T}
            ) i₁))

    e3 : Π (A [ γ ∘ δ ]T) (B [ (γ ∘ δ) ⁺ ]T) ≡ Π (A [ γ ]T [ δ ]T) (B [ γ ⁺ ]T [ δ ⁺ ]T)
    e3 = (λ i → Π ([∘]T-simplest i) (toPathP {A = λ i → Ty (Θ ▹ [∘]T-simplest i)} {x = B [ (γ ∘ δ) ⁺ ]T} (subst-[]T {A = B} {γ = (γ ∘ δ) ⁺} {e = congS (Θ ▹_) [∘]T-simplest} ∙ congS (B [_]T) (fromPathP (∘⁺ {Θ = Θ} {Γ = Γ} {A = A} {γ = γ} {δ = δ})) ∙ [∘]T {A = B} {γ = γ ⁺} {δ = δ ⁺}) i))
  in subst (λ z → Tm Θ (Π (A [ γ∘*δ ]T) (B [ z ]T))) eq2 (f [ γ∘*δ ]Π)
  , toPathP {ℓ-zero} {λ i → Tm Θ (e2 i)} {f [ γ ]Π [ δ ]t} (congS (subst (Tm Θ) e2) (fromPathP⁻ {ℓ-zero} {λ i → Tm Θ (Π[]' i)} {f [ γ ]Π [ δ ]t} {f [ γ ]Π [ δ ]Π} ([]Π {γ = δ} {t = f [ γ ]Π}))
              ∙ sym (substComposite (Tm Θ) symΠ[] e2 (f [ γ ]Π [ δ ]Π))
              ∙ congS (subst (Tm Θ) (symΠ[] ∙ e2)) (sym (fromPathP {ℓ-zero} {_} {f [ γ ∘ δ ]Π} {f [ γ ]Π [ δ ]Π} ([∘]Π {t = f} {γ} {δ})))
              ∙ sym (substComposite (Tm Θ) e3 (symΠ[] ∙ e2) (f [ γ ∘ δ ]Π))
              ∙ congS (subst (Tm Θ) (e3 ∙ symΠ[] ∙ e2)) (fromPathP⁻ {ℓ-zero} {_} {f [ γ ∘ δ ]Π} {f [ γ∘*δ ]Π} (cong (f [_]Π) e1))
              ∙ sym (substComposite (Tm Θ) (λ i → (Π (A [ e1 (~ i) ]T) (B [ e1 (~ i) ⁺ ]T))) (e3 ∙ symΠ[] ∙ e2) (f [ γ∘*δ ]Π))
              ∙ congS (λ e → subst (Tm Θ) e (f [ γ∘*δ ]Π)) (TySet (Π (A [ γ∘*δ ]T) (B [ γ∘*δ ⁺ ]T)) (Π (A [ γ∘*δ ]T) (B [ γ ⁺ ∘ subst (λ z → Sub (Θ ▹ z) (Δ ▹ A [ γ ]T)) eq0 (δ ⁺) ]T)) ((λ i → (Π (A [ e1 (~ i) ]T) (B [ e1 (~ i) ⁺ ]T))) ∙ e3 ∙ symΠ[] ∙ e2) (congS (λ x → Π (A [ γ∘*δ ]T) (B [ x ]T)) eq2)))
