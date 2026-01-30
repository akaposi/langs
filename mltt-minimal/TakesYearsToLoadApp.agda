{-# OPTIONS --cubical --no-postfix-projections --guardedness #-}

module mltt-minimal.TakesYearsToLoadApp where

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

app∙' : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{t : Tm Γ (Π A B)}{a : Tm Γ A}{Γ∙ : ⊤}
        {A∙ : {Δ : Con}(γ : Sub Δ Γ) → Σ (Ty Δ) (A [ γ ]T ≡_)}
        {B∙ : {Δ : Con}(γ : Sub Δ (Γ ▹ A)) → Σ (Ty Δ) (B [ γ ]T ≡_)}
        (t∙ : {Δ : Con}(γ : Sub Δ Γ) → let
          (A[γ]T , eA) = A∙ γ
          γ⁺ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) eA (γ ⁺)
          (B[γ⁺]T , eB) = B∙ γ⁺
        in Σ (Tm Δ (Π A[γ]T B[γ⁺]T))
         (PathP (λ i → Tm Δ ((Π[] ∙ (λ i₁ → Π (eA i₁) (toPathP {A = λ i → Ty (Δ ▹ eA i)} {x = B [ γ ⁺ ]T} (subst-[]T {A = B} {γ = γ ⁺} {e = congS (Δ ▹_) eA} ∙ eB) i₁))) i)) (t [ γ ]t)))
      → (a∙ : {Δ : Con}(γ : Sub Δ Γ) → let
          (A[γ]T , eA) = A∙ γ
          γ⁺ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) eA (γ ⁺)
          (B[γ⁺]T , eB) = B∙ γ⁺
          (t[γ]t , et) = t∙ γ
        in Σ (Tm Δ A[γ]T) (PathP (λ i → Tm Δ (eA i)) (a [ γ ]t)))
      → ∀{Δ}
        (γ : Sub Δ Γ)
      → let
          (A[γ]T , eA) = A∙ γ
          γ⁺ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) eA (γ ⁺)
          (B[γ⁺]T , eB) = B∙ γ⁺
          (t[γ]t , et) = t∙ γ
          (a[γ]t , ea) = a∙ γ
        in Σ (Tm Δ (B [ γ⁺ ∘ ⟨ a[γ]t ⟩ ]T))
           (PathP
             (λ i → Tm Δ (((sym ([∘]T {A = B} {γ = ⟨ a ⟩} {δ = γ}) ∙ congS (B [_]T) (⟨⟩∘ ∙ congS (γ ⁺ ∘_) (congS ⟨_⟩ (fromPathP⁻ ea) ∙ sym (subst-⟨⟩ {A = A[γ]T} {t = a[γ]t} {e = sym eA})) ∙ subst-∘ₘ {γ = γ ⁺} {δ = ⟨ a[γ]t ⟩} {e = congS (Δ ▹_) eA}))) i))
             (app t a [ γ ]t))
app∙' {Γ} {A} {B} {t} {a} {Γ∙} {A∙} {B∙} t∙ a∙ {Δ} γ =
  let
    (A[γ]T , eA) = A∙ γ
    γ⁺ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) eA (γ ⁺)
    (B[γ⁺]T , eB) = B∙ γ⁺
    (t[γ]t , et) = t∙ γ
    (a[γ]t , ea) = a∙ γ
    e0 = congS _[ ⟨ a[γ]t ⟩ ]T (sym eB) ∙ sym ([∘]T {A = B} {γ = γ⁺} {δ = ⟨ a[γ]t ⟩})
    app[]t = fromPathP⁻ (app[] {a = a} {γ = γ} {t = t})
    e1 = sym ([∘]T {A = B} {γ = ⟨ a ⟩} {δ = γ}) ∙ congS (B [_]T) (⟨⟩∘ ∙ congS (γ ⁺ ∘_) (congS ⟨_⟩ (fromPathP⁻ ea) ∙ sym (subst-⟨⟩ {A = A[γ]T} {t = a[γ]t} {e = sym eA})) ∙ subst-∘ₘ {γ = γ ⁺} {δ = ⟨ a[γ]t ⟩} {e = congS (Δ ▹_) eA})
    e2 = Π[] {B = B} ∙ cong₂ Π eA (toPathP (subst-[]T {γ = γ ⁺} {e = congS (Δ ▹_) eA} ∙ eB))
    e3 = congS _[ ⟨ subst (Tm Δ) eA (a [ γ ]t) ⟩ ]T (sym eB) ∙ sym [∘]T
    e4 = congS (λ x → B [ γ⁺ ∘ ⟨ x ⟩ ]T) (fromPathP ea)
    e3∙e4 = e3 ∙ e4
    e5 = sym (subst-Ty-[]T {A = A [ γ ]T} {C = B [ γ ⁺ ]T} {γ = ⟨ a [ γ ]t ⟩} {e = eA})
       ∙ congS (_[_]T (subst (λ z → Ty (Δ ▹ z)) eA (B [ γ ⁺ ]T))) (subst-⟨⟩ {t = a [ γ ]t} {e = eA})
       ∙ congS (_[ ⟨ subst (Tm Δ) eA (a [ γ ]t) ⟩ ]T) (fromPathP {A = λ i → Ty (Δ ▹ eA i)} {x = B [ γ ⁺ ]T} (toPathP {A = λ i → Ty (Δ ▹ eA i)} {x = B [ γ ⁺ ]T} (subst-[]T {A = B} {γ = γ ⁺} {e = congS (Δ ▹_) eA} ∙ eB)))
  in subst (Tm Δ) e0 (app t[γ]t a[γ]t)
   , toPathP (congS (subst (Tm Δ) e1) app[]t
            ∙ sym (substComposite (Tm Δ) (sym [⟨⟩][]T) e1 (app (t [ γ ]Π) (a [ γ ]t)))
            ∙ congS (λ x → subst (Tm Δ) (sym [⟨⟩][]T ∙ e1) (app x (a [ γ ]t))) (sym (fromPathP ([]Π {γ = γ} {t = t})))
            ∙ congS (λ x → subst (Tm Δ) x (app (subst (Tm Δ) Π[] (t [ γ ]t)) (a [ γ ]t))) (TySet (B [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T) (B [ γ⁺ ∘ ⟨ a[γ]t ⟩ ]T) (sym [⟨⟩][]T ∙ e1) (e5 ∙ e3∙e4))
            ∙ substComposite (Tm Δ) e5 e3∙e4 (app (subst (Tm Δ) Π[] (t [ γ ]t)) (a [ γ ]t))
            ∙ congS (subst (Tm Δ) e3∙e4) (subst-app₂ {e1 = eA} {e2 = toPathP (subst-[]T {γ = γ ⁺} {e = congS (Δ ▹_) eA} ∙ eB)} {t = subst (Tm Δ) Π[] (t [ γ ]t)} {a = a [ γ ]t})
            ∙ congS (λ x → subst (Tm Δ) e3∙e4 (app x (subst (Tm Δ) eA (a [ γ ]t)))) (sym (substComposite (Tm Δ) Π[] (cong₂ Π eA (toPathP (subst-[]T {γ = γ ⁺} {e = congS (Δ ▹_) eA} ∙ eB))) (t [ γ ]t))) 
            ∙ substComposite (Tm Δ) e3 e4 (app (subst (Tm Δ) e2 (t [ γ ]t)) (subst (Tm Δ) eA (a [ γ ]t)))
            ∙ fromPathP (cong (λ x → subst (Tm Δ) (congS _[ ⟨ x ⟩ ]T (sym eB) ∙ sym ([∘]T {A = B} {γ = γ⁺} {δ = ⟨ x ⟩})) (app (subst (Tm Δ) e2 (t [ γ ]t)) x)) (fromPathP ea))
            ∙ congS (λ x → subst (Tm Δ) e0 (app x a[γ]t)) (fromPathP et))
