{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

--------- Π stuff -------------------------------
module StricterSyntax.Pi where

open import Lib
open import Syntax
open import DepModel
open I

open import StricterSyntax.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import StricterSyntax.CwF

infixl 9 _[_]Π∙

Π∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A B}(A∙ : Ty∙ Γ∙ n A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B) → Ty∙ Γ∙ n (Π A B)
Π∙ {B} A∙ B∙ = Ty∙.constructor λ {Δ} γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
  in Π A[γ]T B[γ⁺]T ,ₚ Π[] ∙ cong Π $ un $ (cong []Tₑ $ refl $ refl $ (cong (_ ▹_) $ un) $ refl $ coh ∙ un)

Π[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → Π∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ refl $ Π[] ] Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)
Π[]∙ {A} {A∙} {B∙} {γ∙} = cong mkTy∙ $ Π[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,-) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
  in Σ-extₚ (cong (λ y → Π A[γ∘δ]T (L.fst (∣ B∙ ∣ y))) $ (sym coh ∙ cong _⁺ $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh))
            (funext (cong (_≈ _) $ (cong _[ δ ]T $ Π[])))

_[_]Π∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{f Δ}{Δ∙ : Con∙ Δ}{γ}
       → (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)) (f [ γ ]Π)
_[_]Π∙ {A∙} {B∙} f∙ γ∙ = coe (cong (Tm∙ₑ _ _) $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ []Π) (f∙ [ γ∙ ]t∙)

[]Π∙ₑ = λ Γ Γ∙ n A A∙ B B∙ Δ Δ∙ f f∙ γ γ∙ → _[_]Π∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {f} {Δ} {Δ∙} {γ} f∙ γ∙

[]Π∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A B a}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{a∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) a}
        {Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _ _) $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ []Π ] _[_]Π∙ {A∙ = A∙} {B∙ = B∙} a∙ γ∙
[]Π∙ = coh

Π∙ₑ = λ Γ Γ∙ n A A∙ B B∙ → Π∙ {Γ} {Γ∙} {n} {A} {B} A∙ B∙

lam∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b}
       (b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b) → Tm∙ Γ∙ (Π∙ A∙ B∙) (lam b)
lam∙ {A∙} {B} {B∙} {b} b∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (_ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
    (b[γ⁺]t ,-) = ∣ b∙ ∣ γ⁺
  in lam b[γ⁺]t ,ₚ lam[] ∙ cong lamₑ $ refl $ refl $ un $ (cong []Tₑ $ refl $ refl $ (cong (_ ▹_) $ un) $ refl $ coh ∙ un) $ (cong []tₑ $ refl $ (cong (_ ▹_) $ un) $ refl $ refl $ refl $ coh ∙ un)

app∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}{A∙ : Ty∙ Γ∙ n A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{f a}
       (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(a∙ : Tm∙ Γ∙ A∙ a) → Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) (app f a)
app∙ {A∙} {B∙} f∙ a∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (_ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
    (f[γ]t ,-) = ∣ f∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
    (_ ,-) = ∣ B∙ ∣ (γ⁺ ∘ ⟨ a[γ]t ⟩)
  in coe (cong (Tm _) $ (cong _[ ⟨ a[γ]t ⟩ ]T $ sym un ∙ sym [∘]T ∙ un)) (app f[γ]t a[γ]t)
  ,ₚ app[] ∙ cong appₑ $ refl $ refl $ un $ (cong []Tₑ $ refl $ refl $ (cong (_ ▹_) $ un) $ refl $ coh ∙ un) $ (sym coh ∙ un) $ un ∙ coh

lam∙ₑ = λ Γ Γ∙ n A A∙ B B∙ t t∙ → lam∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {t} t∙

app∙ₑ = λ Γ Γ∙ n A A∙ B B∙ f a f∙ a∙ → app∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {f} {a} f∙ a∙

Πβ∙ : ∀{n Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b}{a}{a∙ : Tm∙ Γ∙ A∙ a}
    → app∙ {A∙ = A∙} {B∙ = B∙} (lam∙ {A∙ = A∙} b∙) a∙ ~[ cong (Tm∙ _ _) $ Πβ ] b∙ [ ⟨ a∙ ⟩∙ ]t∙
Πβ∙ {A∙} {B∙} {b∙} {a∙} = cong mkTm∙ $ refl $ Πβ $ funext λ {Δ} → funext λ {γ} →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (_ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
    (b[γ⁺]t ,-) = ∣ b∙ ∣ γ⁺
    (b[γ⁺∘a[γ]]t ,-) = ∣ b∙ ∣ (γ⁺ ∘ ⟨ a[γ]t ⟩)
  in Σ-extₚ (sym coh ∙ Πβ ∙ cong []tₑ $ refl $ refl $ refl $ sym un $ sym un $ refl ∙ sym [∘]t ∙ un) (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Πβ) $ refl $ refl))

Πη∙ : ∀{Γ n}{Γ∙ : Con∙ Γ}{A B f}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f}
    → lam∙ {A∙ = A∙} (app∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ (p∙ {A∙ = A∙})) (q∙ {A∙ = A∙}))
        ~[ cong (Tm∙ₑ _ _) $ (cong (Π _) $ sym [▹η]T) $ refl $ (cong (Π∙ₑ Γ Γ∙ n A A∙) $ sym [▹η]T $ sym ([▹η]T∙ A∙ B∙)) $ Πη ]
      f∙
Πη∙ {Γ} {Γ∙} {A} {B} {f} {A∙} {B∙} {f∙} = cong mkTm∙ₑ
  $ refl
  $ refl
  $ (cong Π $ refl $ sym [▹η]T)
  $ refl
  $ (cong Π∙ₑ $ refl $ refl $ refl $ refl $ reflₑ A∙ $ sym [▹η]T $ sym ([▹η]T∙ A∙ B∙))
  $ Πη
  $ funext λ {Δ} → funext λ {γ} →
    let
      (A[γ]T ,-) = ∣ A∙ ∣ γ
      γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ un) $ refl) (γ ⁺)
      (A[p∘γ⁺]T ,-) = ∣ A∙ ∣ (p ∘ γ⁺) 
      γ⁺⁺ = coe (cong Sub $ (cong (Δ ▹ A[γ]T ▹_) $ (sym [∘]T ∙ un)) $ refl) (γ⁺ ⁺)
      (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
      (B[-]T ,-) = ∣ B∙ ∣ (p ⁺ ∘ (γ⁺⁺ ∘ ⟨ coe (cong (Tm (Δ ▹ A[γ]T)) $ (sym [∘]T ∙ un)) (q [ γ⁺ ]t) ⟩))
      (B[-₂]T ,-) = ∣ B∙ ∣ (p ⁺ ∘ γ⁺⁺)
      (f[γ]t ,-) = ∣ f∙ ∣ γ
      (f[p][γ⁺]Π ,-) = ∣ _[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ (p∙ {A∙ = A∙}) ∣ γ⁺
    in Σ-extₚ (cong lamₑ
                 $ refl
                 $ refl
                 $ refl
                 $ (sym un ∙ cong []Tₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh $ (cong ⟨⟩ₑ $ refl $ refl $ (sym un ∙ [∘]T) $ sym coh) ∙ sym ⟨⟩∘) ∙ sym ass ∙ cong (_∘ γ⁺) $ sym ▹η ∙ idl) ∙ un ∙ [▹η]T)
                 $ (sym coh
                   ∙ cong appₑ
                       $ refl
                       $ refl
                       $ (sym un ∙ [∘]T ∙ cong []Tₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ weave p∘⁺ ∙ cong []Tₑ $ refl $ refl $ (cong (Δ ▹_) $ un) $ un $ (cong pₑ $ refl $ refl $ un))
                       $ (sym un ∙ [∘]T ∙ cong []Tₑ $ refl $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh ∙ sym [∘]T ∙ cong []Tₑ $ refl $ refl $ (cong (λ x y → Δ ▹ x ▹ y) $ sym un $ (sym [∘]T ∙ cong []Tₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ p∘⁺) ∙ [∘]T)) $ refl $ (sym ∘⁺ ∙ cong ⁺ₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ p∘⁺) ∙ ∘⁺) ∙ [∘]T ∙ cong []Tₑ $ (cong (Δ ▹_) $ un) $ refl $ (cong (λ x y → Δ ▹ x ▹ y) $ un $ (cong []Tₑ $ refl $ refl $ (cong (Δ ▹_) $ un) $ un $ (cong pₑ $ refl $ refl $ un))) $ (cong []Tₑ $ refl $ refl $ (cong (Δ ▹_) $ un) $ refl $ coh ∙ un) $ (cong ⁺ₑ $ refl $ (cong (Δ ▹_) $ un) $ refl $ un $ (cong pₑ $ refl $ refl $ un)))
                       $ (sym un ∙ cong []tₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym Π[] $ sym []Π $ sym coh ∙ weave-t p∘⁺ ∙ cong []tₑ $ refl $ (cong (Δ ▹_) $ un) $ refl $ (Π[] ∙ cong Π $ un $ (cong []Tₑ $ refl $ refl $ (cong (Δ ▹_) $ un) $ refl $ coh ∙ un)) $ un $ (cong pₑ $ refl $ refl $ un) ∙ coh)
                       $ (sym coh ∙ cong []tₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ refl $ refl $ sym coh ∙ q[⁺] ∙ cong qₑ $ refl $ refl $ un))
             ∙ Πη) (funextₕ (cong (Tm Δ) $ (cong (Π A[γ]T) $ (sym un ∙ cong ([]Tₑ _ _ _ _) $ (cong (∘ₑ _ _ _ _) $ (cong ∘ₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh $ (cong ⟨⟩ₑ $ refl $ refl $ (sym un ∙ [∘]T) $ sym coh) ∙ sym ⟨⟩∘) ∙ sym ass ∙ cong (_∘ γ⁺) $ sym ▹η ∙ idl) ∙ un)))
                            λ e → cong ~ₑ $ (cong (Tm Δ) $ (cong (λ x → Π A x [ γ ]T) $ annihilate (sym ▹η)))
                                          $ (cong []tₑ $ refl $ refl $ refl $ (cong (Π A) $ annihilate (sym ▹η)) $ Πη $ refl)
                                          $ (cong (Tm Δ) $ (cong (Π A[γ]T) $ (sym un ∙ cong []Tₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh $ (cong ⟨⟩ₑ $ refl $ refl $ (sym un ∙ [∘]T) $ sym coh) ∙ sym ⟨⟩∘) ∙ sym ass ∙ cong (_∘ γ⁺) $ sym ▹η ∙ idl) ∙ un)))
                                          $ e)

lam[]∙ : ∀{n Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → lam∙ {A∙ = A∙} b∙ [ γ∙ ]t∙
           ~[ cong (Tm∙ₑ _) $ refl $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ lam[] ]
         lam∙ {A∙ = A∙ [ γ∙ ]T∙} (b∙ [ _⁺∙ {A∙ = A∙} γ∙ ]t∙)
lam[]∙ {A} {A∙} {B∙} {b∙} {γ} {γ∙} = cong mkTm∙ₑ $ refl $ refl $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ lam[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,-) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
    δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl) (δ ⁺)
    γ∘δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ un) $ refl) (γ∘δ ⁺)
    (B[γ∘δ⁺]T ,-) = ∣ B∙ ∣ γ∘δ⁺
    (B[γ⁺∘δ⁺]T ,-) = ∣ B∙ ∣ (γ ⁺ ∘ δ⁺)
    (b[γ∘δ⁺]t ,-) = ∣ b∙ ∣ γ∘δ⁺
    (b[γ⁺∘δ⁺]t ,-) = ∣ b∙ ∣ (γ ⁺ ∘ δ⁺)
    pr1 = sym coh ∙ cong ⁺ₑ $ refl $ refl $ refl $ refl $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh
  in Σ-extₚ (cong lamₑ $ refl $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1) $ (cong (λ x y → L.fst (∣ b∙ ∣ {x} y)) $ refl $ pr1))
            (funextₕ (cong (Tm Θ) $ (cong (Π A[γ∘δ]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1))) λ e → cong ~ₑ $ (cong (λ x → Tm Θ (x [ δ ]T)) $ Π[]) $ (cong []tₑ $ refl $ refl $ refl $ Π[] $ lam[] $ refl) $ (cong (Tm Θ) $ (cong (Π A[γ∘δ]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1))) $ e)

-------------- app magic ------------------
app'∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{n A}(A∙ : Ty∙ Γ∙ n A){B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b}(b∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) b)
      → Tm∙ (Γ∙ ▹∙ A∙) B∙ (app' b)
app'∙ A∙ {B∙} b∙ = coe (cong Tm∙ₑ $ refl $ refl $ sym [▹η]T $ refl $ sym ([▹η]T∙ A∙ B∙) $ coh) (app∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} b∙ (p∙ {A∙ = A∙})) (q∙ {A∙ = A∙}))

app'∙ₑ = λ Γ Γ∙ n A A∙ B B∙ b b∙ → app'∙ {Γ} {Γ∙} {n} {A} A∙ {B} {B∙} {b} b∙

app'β∙ : ∀{n Γ A B}{Γ∙ : Con∙ Γ}(A∙ : Ty∙ Γ∙ n A){B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b}
       → app'∙ A∙ (lam∙ {A∙ = A∙} b∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'β ] b∙
app'β∙ A∙ {B∙} {b∙} = sym coh ∙ cong app∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ reflₑ (B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙) $ (sym []Π ∙ lam[]) $ refl $ (sym ([]Π∙ {A∙ = A∙} {B∙ = B∙} {a∙ = lam∙ {A∙ = A∙} b∙} {γ∙ = p∙ {A∙ = A∙}}) ∙ (lam[]∙ {A∙ = A∙} {b∙ = b∙} {γ∙ = p∙ {A∙ = A∙}})) $ reflₑ (q∙ {A∙ = A∙}) ∙ Πβ∙ {b∙ = b∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]t∙} {a∙ = q∙ {A∙ = A∙}} ∙ sym ([▹η]t∙ A∙ b∙)

app'η∙ : ∀{Γ n}{Γ∙ : Con∙ Γ}{A B b}(A∙ : Ty∙ Γ∙ n A){B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) b}
       → lam∙ {A∙ = A∙} {B∙ = B∙} (app'∙ A∙ b∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'η ] b∙
app'η∙ A∙ {B∙} {b∙} = cong lam∙ₑ $ refl $ refl $ refl $ refl $ reflₑ A∙ $ [▹η]T $ [▹η]T∙ A∙ B∙ $ sym coh $ sym coh ∙ Πη∙ {A∙ = A∙} {B∙ = B∙} {f∙ = b∙}

app'[]∙ : ∀{Γ n}{Γ∙ : Con∙ Γ}{A B b}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{b∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) b}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        → _[_]t∙ {A∙ = B∙} (app'∙ A∙ b∙) (_⁺∙ {A∙ = A∙} γ∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'[] ] app'∙ (A∙ [ γ∙ ]T∙) (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} b∙ γ∙)
app'[]∙ {(Γ)} {(n)} {(Γ∙)} {(A)} {(B)} {(b)} {(A∙)} {(B∙)} {(b∙)} {(Δ)} {(Δ∙)} {(γ)} {(γ∙)} =
        sym (app'β∙ (A∙ [ γ∙ ]T∙))
      ∙ sym coh
      ∙ cong app∙ₑ
          $ refl
          $ refl
          $ refl
          $ refl
          $ refl
          $ refl
          $ reflₑ (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙ [ _⁺∙ {A∙ = A∙ [ γ∙ ]T∙} (p∙ {A∙ = A∙ [ γ∙ ]T∙}) ]T∙)
          $ (cong _[ p ]Π $ (sym lam[] ∙ cong _[ γ ]t $ app'η ∙ []Π))
          $ refl
          $[ _
           , _[_]Π∙ {A∙ = A∙ [ γ∙ ]T∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} b∙ γ∙) (p∙ {A∙ = A∙ [ γ∙ ]T∙})
           ] (cong []Π∙ₑ
                $ refl
                $ refl
                $ refl
                $ refl
                $ reflₑ (A∙ [ γ∙ ]T∙)
                $ refl
                $ reflₑ (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)
                $ refl
                $ refl
                $ (sym lam[] ∙ cong _[ γ ]t $ app'η ∙ []Π)
                $[ _
                 , _[_]Π∙ {A∙ = A∙} {B∙ = B∙} b∙ γ∙
                 ] (sym (lam[]∙ {A∙ = A∙} {B∙ = B∙} {b∙ = app'∙ A∙ b∙} {γ∙ = γ∙})
                  ∙ cong []t∙ₑ
                      $ refl
                      $ refl
                      $ refl
                      $ refl
                      $ refl
                      $ app'η
                      $ refl
                      $ refl
                      $ refl
                      $[ _ , b∙ ] app'η∙ A∙
                      $ reflₑ γ∙
                  ∙ []Π∙ {A∙ = A∙} {B∙ = B∙} {a∙ = b∙} {γ∙ = γ∙})
                $ refl
                $ reflₑ (p∙ {A∙ = A∙ [ γ∙ ]T∙}))
          $ reflₑ (q∙ {A∙ = A∙ [ γ∙ ]T∙})
      ∙ coh


app'≈app∙ : ∀{Γ n}{Γ∙ : Con∙ Γ}{A B b}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}(b∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) b){a}(a∙ : Tm∙ Γ∙ A∙ a)
          → _[_]t∙ {A∙ = B∙} (app'∙ A∙ b∙) ⟨ a∙ ⟩∙ ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'≈app ] app∙ {B∙ = B∙} b∙ a∙
app'≈app∙ {A} {B} {A∙} {B∙} b∙ a∙ =
            cong []t∙ₑ
               $ refl
               $ refl
               $ refl
               $ [▹η]T
               $ [▹η]T∙ A∙ B∙
               $ sym coh
               $ refl
               $ refl
               $ refl
               $ sym coh
               $ reflₑ ⟨ a∙ ⟩∙
           ∙ sym (Πβ∙ {A∙ = A∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙ [ ⟨ q∙ {A∙ = A∙} ⟩∙ ]T∙} {b∙ = app∙ {A∙ = A∙ [ p∙ {A∙ = A∙} ]T∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} b∙ (p∙ {A∙ = A∙})) (q∙ {A∙ = A∙})} {a∙ = a∙})
           ∙ cong app∙ₑ
               $ refl
               $ refl
               $ refl
               $ refl
               $ refl
               $ sym [▹η]T
               $ sym ([▹η]T∙ A∙ B∙)
               $ Πη
               $ refl
               $[ lam∙ {A∙ = A∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙ [ ⟨ q∙ {A∙ = A∙} ⟩∙ ]T∙} (app∙ {A∙ = A∙ [ p∙ {A∙ = A∙} ]T∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} b∙ (p∙ {A∙ = A∙})) (q∙ {A∙ = A∙})) , b∙ ] Πη∙ {A∙ = A∙} {B∙ = B∙}
               $ reflₑ a∙

app[]∙ : ∀{Γ n}{Γ∙ : Con∙ Γ}{A B f}{A∙ : Ty∙ Γ∙ n A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B}{f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f}{a}{a∙ : Tm∙ Γ∙ A∙ a}
          {Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → app∙ {B∙ = B∙} f∙ a∙ [ γ∙ ]t∙
           ~[ cong (Tm∙ₑ _ _) $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ B∙ a∙ γ∙ $ app[] ]
         app∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ γ∙) (a∙ [ γ∙ ]t∙)
app[]∙ {Γ} {A} {B} {A∙} {B∙} {f∙} {a∙} {γ∙} =
    cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ sym app'≈app $ refl $ refl $ refl $ sym (app'≈app∙ f∙ a∙) $ reflₑ γ∙
  ∙ [⟨⟩][]t∙ (app'∙ A∙ f∙) a∙ γ∙
  ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'[] $ refl $ refl $ refl $ app'[]∙ {A∙ = A∙} {B∙ = B∙} {b∙ = f∙} {γ∙ = γ∙} $ reflₑ ⟨ a∙ [ γ∙ ]t∙ ⟩∙
  ∙ app'≈app∙ (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ γ∙) (a∙ [ γ∙ ]t∙)
