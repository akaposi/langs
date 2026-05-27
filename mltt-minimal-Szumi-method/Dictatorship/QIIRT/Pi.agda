{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

--------- Π stuff -------------------------------
module Dictatorship.QIIRT.Pi where

open import Lib
open import Dictatorship.Syntax
open import Dictatorship.DepModel
open I

open import Dictatorship.QIIRT.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import Dictatorship.QIIRT.CwF

infixl 9 _[_]Π∙

Π∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Π A B)
Π∙ {B} A∙ B∙ = Ty∙.constructor λ {Δ} γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
  in Π A[γ]T B[γ⁺]T ,ₚ Π[] ∙ cong Π $ un $ (cong []Tₑ $ refl $ (cong (_ ▹_) $ un) $ refl $ coh ∙ un)

Π[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → Π∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Π[] ] Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)
Π[]∙ {A} {A∙} {B∙} {γ∙} = cong mkTy∙ $ Π[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,-) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
  in Σ-extₚ (cong (λ y → Π A[γ∘δ]T (L.fst (∣ B∙ ∣ y))) $ (sym coh ∙ cong _⁺ $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh))
            (funext (cong (_≈ _) $ (cong _[ δ ]T $ Π[])))

_[_]Π∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{f Δ}{Δ∙ : Con∙ Δ}{γ}
       → (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)) (f [ γ ]Π)
_[_]Π∙ {A∙} {B∙} f∙ γ∙ = coe (cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ []Π) (f∙ [ γ∙ ]t∙)

[]Π∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B a}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) a}
        {Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ []Π ] _[_]Π∙ {A∙ = A∙} {B∙ = B∙} a∙ γ∙
[]Π∙ = coh

Π∙ₑ = λ Γ Γ∙ A A∙ B B∙ → Π∙ {Γ} {Γ∙} {A} {B} A∙ B∙

lam∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b}
       (b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b) → Tm∙ Γ∙ (Π∙ A∙ B∙) (lam b)
lam∙ {A∙} {B} {B∙} {b} b∙ = Tm∙.constructor λ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (_ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
    (b[γ⁺]t ,-) = ∣ b∙ ∣ γ⁺
  in lam b[γ⁺]t ,ₚ lam[] ∙ cong lamₑ $ refl $ un $ (cong []Tₑ $ refl $ (cong (_ ▹_) $ un) $ refl $ coh ∙ un) $ (cong []tₑ $ refl $ (cong (_ ▹_) $ un) $ refl $ refl $ coh ∙ un)

app∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{f a}
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
  ,ₚ app[] ∙ cong appₑ $ refl $ un $ (cong []Tₑ $ refl $ (cong (_ ▹_) $ un) $ refl $ coh ∙ un) $ (sym coh ∙ un) $ un ∙ coh

Πβ∙ : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b}{a}{a∙ : Tm∙ Γ∙ A∙ a}
    → app∙ {A∙ = A∙} {B∙ = B∙} (lam∙ {A∙ = A∙} b∙) a∙ ~[ cong (Tm∙ _ _) $ Πβ ] b∙ [ ⟨ a∙ ⟩∙ ]t∙
Πβ∙ {A∙} {B∙} {b∙} {a∙} = cong mkTm∙ $ refl $ Πβ $ funext λ {Δ} → funext λ {γ} →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    (a[γ]t ,-) = ∣ a∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (_ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
    (b[γ⁺]t ,-) = ∣ b∙ ∣ γ⁺
    (b[γ⁺∘a[γ]]t ,-) = ∣ b∙ ∣ (γ⁺ ∘ ⟨ a[γ]t ⟩)
  in Σ-extₚ (sym coh ∙ Πβ ∙ cong []tₑ $ refl $ refl $ sym un $ sym un $ refl ∙ sym [∘]t ∙ un) (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Πβ) $ refl $ refl))
  
Πη∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B f}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f}
    → lam∙ {A∙ = A∙} (app∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} (p∙ {A∙ = A∙}) ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ (p∙ {A∙ = A∙})) (q∙ {A∙ = A∙}))
        ~[ cong (Tm∙ₑ _) $ (cong (Π _) $ sym [▹η]T) $ refl $ (cong (Π∙ₑ Γ Γ∙ A A∙) $ sym [▹η]T $ sym ([▹η]T∙ A∙ B∙)) $ Πη ]
      f∙
Πη∙ {Γ} {Γ∙} {A} {B} {f} {A∙} {B∙} {f∙} = cong mkTm∙ₑ
  $ refl
  $ (cong Π $ refl $ sym [▹η]T)
  $ refl
  $ (cong Π∙ₑ $ refl $ refl $ refl $ reflₑ A∙ $ sym [▹η]T $ sym ([▹η]T∙ A∙ B∙))
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
      (f[p∘γ⁺]t ,ₚ proof) = ∣ f∙ ∣ (p ∘ γ⁺)
    in Σ-extₚ (cong lamₑ
                 $ refl
                 $ refl
                 $ (sym un ∙ cong []Tₑ $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh $ (cong ⟨⟩ₑ $ refl $ (sym un ∙ [∘]T) $ sym coh) ∙ sym ⟨⟩∘) ∙ sym ass ∙ cong (_∘ γ⁺) $ sym ▹η ∙ idl) ∙ un ∙ [▹η]T)
                 $ (sym coh ∙ cong appₑ
                                $ refl
                                $ (sym un ∙ [∘]T ∙ cong []Tₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ weave p∘⁺ ∙ cong []Tₑ $ refl $ (cong (Δ ▹_) $ un) $ un $ (cong pₑ $ refl $ un))
                                $ (sym un ∙ [∘]T ∙ cong []Tₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh ∙ sym [∘]T ∙ cong []Tₑ $ refl $ (cong (λ x y → Δ ▹ x ▹ y) $ sym un $ (sym [∘]T ∙ cong []Tₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ p∘⁺) ∙ [∘]T)) $ refl $ (sym ∘⁺ ∙ cong ⁺ₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ p∘⁺) ∙ ∘⁺) ∙ [∘]T ∙ cong []Tₑ $ (cong (Δ ▹_) $ un) $ (cong (λ x y → Δ ▹ x ▹ y) $ un $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ un) $ un $ (cong pₑ $ refl $ un))) $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ un) $ refl $ coh ∙ un) $ (cong ⁺ₑ $ refl $ (cong (Δ ▹_) $ un) $ un $ (cong pₑ $ refl $ un)))
                                $ (cong (L.fstₑ {_} {lzero}) $ (cong (Tm (Δ ▹ A[γ]T)) $ (cong (Π A[p∘γ⁺]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh ∙ sym ∘⁺ ∙ coh))))
                                                             $ (funextₕ (cong (Tm (Δ ▹ A[γ]T)) $ (cong (Π A[p∘γ⁺]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh ∙ sym ∘⁺ ∙ coh)))) λ e → cong Lift $ (cong ~ₑ $ (cong (Tm (Δ ▹ A[γ]T)) $ (cong []Tₑ $ refl $ refl $ sym Π[] $ refl)) $ (cong []tₑ $ refl $ refl $ sym Π[] $ sym []Π $ refl) $ (cong (Tm (Δ ▹ A[γ]T)) $ (cong (Π A[p∘γ⁺]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh ∙ sym ∘⁺ ∙ coh)))) $ e))
                                                             $ (cong Tm∙∣∣ₑ
                                                                  $ reflₑ (Γ ▹ A)
                                                                  $ sym Π[]
                                                                  $ reflₑ (Γ∙ ▹∙ A∙)
                                                                  $ sym (Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = p∙ {A∙ = A∙}})
                                                                  $ sym []Π
                                                                  $ (sym ([]Π∙ {A∙ = A∙} {B∙ = B∙} {a∙ = f∙} {γ∙ = p∙ {A∙ = A∙}}))
                                                                  $ reflₑ (Δ ▹ A[γ]T) $ reflₑ γ⁺)
                                                              ∙ reflₑ (L.fst (∣ f∙ [ p∙ {A∙ = A∙} ]t∙ ∣ γ⁺))
                                                              ∙ sym proof
                                                              ∙ cong []tₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ refl $ (cong ∘ₑ $ refl $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ sym coh ∙ p∘⁺)
                                                              ∙ [∘]t
                                                              ∙ cong []tₑ $ refl $ (cong (Δ ▹_) $ un) $ (Π[] ∙ cong Π $ un $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ un) $ refl $ coh ∙ un)) $ un $ (cong pₑ $ refl $ un)
                                                              ∙ coh)
                                $ (sym coh ∙ cong []tₑ $ refl $ (cong (Δ ▹_) $ sym un) $ refl $ refl $ sym coh ∙ q[⁺] ∙ cong qₑ $ refl $ un))
              ∙ Πη)
              (funextₕ (cong (Tm Δ) $ (cong (Π A[γ]T) $ (sym un ∙ cong ([]Tₑ _ _ _) $ (cong ∘ₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh $ (cong ⟨⟩ₑ $ refl $ (sym un ∙ [∘]T) $ sym coh) ∙ sym ⟨⟩∘) ∙ sym ass ∙ cong (_∘ γ⁺) $ sym ▹η ∙ idl) ∙ un)))
                       λ e → cong ~ₑ $ (cong (Tm Δ) $ (cong []Tₑ $ refl $ refl $ (cong (Π A) $ annihilate (sym ▹η)) $ refl)) $ (cong []tₑ $ refl $ refl $ (cong (Π A) $ annihilate (sym ▹η)) $ Πη $ refl) $ (cong (Tm Δ) $ (cong (Π A[γ]T) $ (sym un ∙ cong []Tₑ $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ refl $ refl $ refl $ (cong ∘ₑ $ refl $ (cong (Δ ▹ A[γ]T ▹_) $ (sym un ∙ [∘]T)) $ refl $ sym coh $ (cong ⟨⟩ₑ $ refl $ (sym un ∙ [∘]T) $ sym coh) ∙ sym ⟨⟩∘) ∙ sym ass ∙ cong (_∘ γ⁺) $ sym ▹η ∙ idl) ∙ un))) $ e)

lam[]∙ : ∀{Γ A B}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b}{b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → lam∙ {A∙ = A∙} b∙ [ γ∙ ]t∙
           ~[ cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ lam[] ]
         lam∙ {A∙ = A∙ [ γ∙ ]T∙} (b∙ [ _⁺∙ {A∙ = A∙} γ∙ ]t∙)
lam[]∙ {A} {A∙} {B∙} {b∙} {γ} {γ∙} = cong mkTm∙ₑ $ refl $ Π[] $ refl $ Π[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ lam[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,-) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
    δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ un) $ refl) (δ ⁺)
    γ∘δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ un) $ refl) (γ∘δ ⁺)
    (B[γ∘δ⁺]T ,-) = ∣ B∙ ∣ γ∘δ⁺
    (B[γ⁺∘δ⁺]T ,-) = ∣ B∙ ∣ (γ ⁺ ∘ δ⁺)
    (b[γ∘δ⁺]t ,-) = ∣ b∙ ∣ γ∘δ⁺
    (b[γ⁺∘δ⁺]t ,-) = ∣ b∙ ∣ (γ ⁺ ∘ δ⁺)
    pr1 = sym coh ∙ cong ⁺ₑ $ refl $ refl $ refl $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh
  in Σ-extₚ (cong lamₑ $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1) $ (cong (λ x y → L.fst (∣ b∙ ∣ {x} y)) $ refl $ pr1))
            (funextₕ (cong (Tm Θ) $ (cong (Π A[γ∘δ]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1))) λ e → cong ~ₑ $ (cong (λ x → Tm Θ (x [ δ ]T)) $ Π[]) $ (cong []tₑ $ refl $ refl $ Π[] $ lam[] $ refl) $ (cong (Tm Θ) $ (cong (Π A[γ∘δ]T) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1))) $ e)

app[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B f}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f}{a}{a∙ : Tm∙ Γ∙ A∙ a}
          {Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → app∙ {B∙ = B∙} f∙ a∙ [ γ∙ ]t∙
           ~[ cong (Tm∙ₑ _) $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ $ app[] ]
         app∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (_[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ γ∙) (a∙ [ γ∙ ]t∙)
app[]∙ {Γ} {A} {B} {A∙} {B∙} {f∙} {a∙} {γ∙} = cong mkTm∙ₑ
  $ refl
  $ weave ⟨⟩∘
  $ refl
  $ weave∙ B∙ ⟨ a∙ ⟩∙ γ∙ (_⁺∙ {A∙ = A∙} γ∙) ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ⟨⟩∘ (⟨⟩∘∙ {a∙ = a∙} {γ∙ = γ∙})
  $ app[]
  $ funext λ {Θ} → funext λ {δ} →
    let
      (γ∘δ ,-) = ∣ γ∙ ∣ δ
      (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
      δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ un) $ refl) (δ ⁺)
      γ∘δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ un) $ refl) (γ∘δ ⁺)
      (a[γ∘δ]t ,-) = ∣ a∙ ∣ γ∘δ
      (f[γ∘δ]t ,-) = ∣ f∙ ∣ γ∘δ
      (f[γ][δ]t ,-) = ∣ _[_]Π∙ {A∙ = A∙} {B∙ = B∙} f∙ γ∙ ∣ δ
      pr1 = sym coh ∙ cong ⁺ₑ $ refl $ refl $ refl $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh
    in Σ-extₚ (sym coh ∙ cong appₑ $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ pr1) $ (sym un ∙ cong []tₑ $ refl $ refl $ refl $ refl $ sym un ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ Π[] $ []Π $ refl ∙ un) $ refl ∙ coh)
              (funextₕ (cong (Tm Θ) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (cong (_∘ ⟨ a[γ∘δ]t ⟩) $ pr1 ∙ ass))) λ e → cong ~ₑ $ (cong (Tm Θ) $ (cong []Tₑ $ refl $ refl $ weave ⟨⟩∘ $ refl)) $ (cong []tₑ $ refl $ refl $ weave ⟨⟩∘ $ app[] $ refl) $ (cong (Tm Θ) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (cong (_∘ ⟨ a[γ∘δ]t ⟩) $ pr1 ∙ ass))) $ e)
