{-# OPTIONS --cubical --no-postfix-projections --guardedness #-}

module mltt-minimal.TakesYearsToLoadLam where

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

lam∙' : ∀{Γ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{t : Tm (Γ ▹ A) B}{Γ∙ : ⊤}
        {A∙ : {Δ : Con}(γ : Sub Δ Γ) → Σ (Ty Δ) (A [ γ ]T ≡_)}
        {B∙ : {Δ : Con}(γ : Sub Δ (Γ ▹ A)) → Σ (Ty Δ) (B [ γ ]T ≡_)}
        (t∙ : {Δ : Con}(γ : Sub Δ (Γ ▹ A)) → Σ (Tm Δ (fst (B∙ γ))) (PathP (λ i → Tm Δ (snd (B∙ γ) i)) (t [ γ ]t)))
        {Δ}
        (γ : Sub Δ Γ)
      → let
          (A[γ]T , e1) = A∙ γ
          γ⁺ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺)
          (B[γ⁺]T , e2) = B∙ γ⁺

          subst-[]T1 : subst Ty (λ i → Δ ▹ e1 i) (B [ γ ⁺ ]T) ≡ B [ subst (λ z → Sub z (Γ ▹ A)) (λ i → Δ ▹ e1 i) (γ ⁺) ]T
          subst-[]T1 = subst-[]T {Γ = Γ ▹ A} {Δ = Δ ▹ A [ γ ]T} {A = B} {γ = γ ⁺} {e = congS (Δ ▹_) e1}
        in Σ (Tm Δ (Π A[γ]T B[γ⁺]T))
             (PathP (λ i → Tm Δ ((Π[] {B = B} ∙ (λ i₁ → Π (e1 i₁) (toPathP {A = λ i → Ty (Δ ▹ e1 i)} {x = B [ γ ⁺ ]T} (subst-[]T1 ∙ e2) i₁))) i)) (lam t [ γ ]t))
lam∙' {Γ} {A} {B} {t} {Γ∙} {A∙} {B∙} t∙ {Δ} γ =
  let
    (A[γ]T , e1) = A∙ γ
    γ⁺ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺)
    (B[γ⁺]T , e2) = B∙ γ⁺
    (t[γ⁺]t , e3) = t∙ γ⁺

    subst-fillerT : PathP (λ i → Ty (Δ ▹ e1 i)) (B [ γ ⁺ ]T) (subst Ty (λ i₁ → Δ ▹ e1 i₁) (B [ γ ⁺ ]T))
    subst-fillerT = subst-filler Ty (λ i₁ → Δ ▹ e1 i₁) (B [ γ ⁺ ]T)
    
    t[γ⁺]t-subst : Tm (Δ ▹ A[γ]T) (subst Ty (λ i₁ → Δ ▹ e1 i₁) (B [ γ ⁺ ]T))
    t[γ⁺]t-subst = transport (λ i → Tm (Δ ▹ e1 i) (subst-fillerT i)) (t [ γ ⁺ ]t)

    subst-[]T1 : subst Ty (λ i → Δ ▹ e1 i) (B [ γ ⁺ ]T) ≡ B [ subst (λ z → Sub z (Γ ▹ A)) (λ i → Δ ▹ e1 i) (γ ⁺) ]T
    subst-[]T1 = subst-[]T {Γ = Γ ▹ A} {Δ = Δ ▹ A [ γ ]T} {A = B} {γ = γ ⁺} {e = congS (Δ ▹_) e1}
  in lam t[γ⁺]t
   , toPathP (
     congS (subst (Tm Δ) (Π[] ∙ (λ i₁ → Π (e1 i₁) (toPathP {A = λ i → Ty (Δ ▹ e1 i)} {x = B [ γ ⁺ ]T} (subst-[]T1 ∙ e2) i₁)))) (fromPathP⁻ (lam[] {b = t}))
   ∙ sym (substComposite (Tm Δ) (sym Π[]) (Π[] ∙ (λ i₁ → Π (e1 i₁) (toPathP {A = λ i → Ty (Δ ▹ e1 i)} {x = B [ γ ⁺ ]T} (subst-[]T1 ∙ e2) i₁))) (lam (t [ γ ⁺ ]t)))
   ∙ congS (λ x → subst (Tm Δ) x (lam (t [ γ ⁺ ]t))) (TySet (Π (A [ γ ]T) (B [ γ ⁺ ]T)) (Π A[γ]T B[γ⁺]T) ((λ i → Π[] {A = A} {B = B} {γ = γ} (~ i)) ∙ Π[] ∙ (λ i₁ → Π (e1 i₁) (toPathP {A = λ i → Ty (Δ ▹ e1 i)} {x = B [ γ ⁺ ]T} (subst-[]T1 ∙ e2) i₁))) ((λ i → Π (e1 i) (subst-fillerT i)) ∙ (λ i → Π A[γ]T (subst-[]T1 i)) ∙ (λ i → Π A[γ]T (e2 i)))) 
   ∙ substComposite (Tm Δ) (cong₂ Π e1 subst-fillerT) (congS (Π A[γ]T) subst-[]T1 ∙ congS (Π A[γ]T) e2) (lam (t [ γ ⁺ ]t))
   ∙ congS {y = lam t[γ⁺]t-subst} (subst (Tm Δ) (congS (Π A[γ]T) subst-[]T1 ∙ congS (Π A[γ]T) e2)) (subst₂-lam {Γ = Δ} {t = t [ γ ⁺ ]t} {e1 = e1} {e2 = subst-fillerT})
   ∙ substComposite (Tm Δ) (congS (Π A[γ]T) subst-[]T1) (congS (Π A[γ]T) e2) (lam t[γ⁺]t-subst)
   ∙ congS (subst (Tm Δ) (congS (Π A[γ]T) e2)) (subst-lam {Γ = Δ} {A = A[γ]T} {t = t[γ⁺]t-subst} {e = subst-[]T1})
   ∙ congS (λ x → subst (Tm Δ) (congS (Π A[γ]T) e2) (lam x)) (fromPathP (subst-Sub-[]t {Γ = Γ ▹ A} {A = B} {t = t} {γ = γ ⁺} {e = congS (Δ ▹_) e1}))
   ∙ subst-lam {Δ} {A[γ]T} {t = t [ γ⁺ ]t} {e2}
   ∙ congS lam (fromPathP e3)
   )
