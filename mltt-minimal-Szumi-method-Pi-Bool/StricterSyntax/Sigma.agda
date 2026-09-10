{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

------- ⊤ Σ stuff ---------------------------
module Dictatorship.QIIRT.Sigma where

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

infixr 5 _,∙_

⊤∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Ty∙ Γ∙ ⊤
⊤∙ = Ty∙.constructor (λ _ → ⊤ ,ₚ ⊤[])
  
⊤[]∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → ⊤∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊤[] ] ⊤∙
⊤[]∙ {γ∙} = cong mkTy∙ $ ⊤[] $ funext λ {Θ} → funext λ {δ} →
  Σ-extₚ refl (funext λ {z} → cong (_≈ z) $ (cong _[ δ ]T $ ⊤[]))
  
tt∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ ⊤∙ tt
tt∙ = Tm∙.constructor (λ _ → tt ,ₚ tt[])

⊤η∙ : ∀{Γ a}{Γ∙ : Con∙ Γ}{a∙ : Tm∙ Γ∙ ⊤∙ a}
    → a∙ ~[ cong Tm∙ₑ $ reflₑ Γ $ refl $ reflₑ Γ∙ $ refl $ ⊤η ] tt∙
⊤η∙ = cong mkTm∙ $ refl $ ⊤η $ funext λ {Δ} → funext λ {γ} →
  Σ-extₚ ⊤η (funext λ {z} → cong ~ₑ $ refl $ (cong _[ γ ]t $ ⊤η) $ refl $ refl)

Σ∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B}(A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Σ A B)
Σ∙ {B} A∙ B∙ = mkTy∙ _ λ Δ γ →
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ un) $ refl) (γ ⁺)
    (B[γ⁺]T ,-) = ∣ B∙ ∣ γ⁺
  in Σ A[γ]T B[γ⁺]T ,ₚ Σ[] ∙ cong Σ $ un $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ un) $ refl $ coh ∙ un)

Σ[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{Δ}{Δ∙ : Con∙ Δ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → Σ∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Σ[] ] Σ∙ (A∙ [ γ∙ ]T∙) (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)
Σ[]∙ {A} {A∙} {B∙} {γ∙} = cong mkTy∙ $ Σ[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,-) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,-) = ∣ A∙ ∣ γ∘δ
  in Σ-extₚ
       (cong (Σ _) $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ un ∙ un)) $ refl $ coh)))
       (funext λ {z} → cong (_≈ z) $ (cong _[ δ ]T $ Σ[]))

_,∙_ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{a B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b}
       (a∙ : Tm∙ Γ∙ A∙ a)(b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b)
     → Tm∙ Γ∙ (Σ∙ A∙ B∙) (a , b)
_,∙_ {A∙} {B} {B∙} a∙ b∙ = Tm∙.constructor (λ {Δ} γ →
  let
    (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
    (B[γ⁺]T ,ₚ ≈B[γ⁺]T) = ∣ B∙ ∣ γ⁺
    (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    (B[γ⁺∘⟨a[γ]t⟩]T ,ₚ ≈B[γ⁺∘⟨a[γ]t⟩]T) = ∣ B∙ ∣ (γ⁺ ∘ ⟨ a[γ]t ⟩)
    (b[γ]t ,ₚ ≈b[γ]t) = ∣ b∙ ∣ γ
  in a[γ]t , coe (cong (Tm Δ) $ (sym ≈B[γ⁺∘⟨a[γ]t⟩]T ∙ [∘]T ∙ cong (_[ ⟨ a[γ]t ⟩ ]T) $ ≈B[γ⁺]T)) b[γ]t ,ₚ ,[] ∙ cong ,ₑ $ refl $ ≈A[γ]T $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh ∙ ≈B[γ⁺]T) $ ≈a[γ]t $ (sym coh ∙ ≈b[γ]t ∙ coh))
  
,[]∙ : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a}{a∙ : Tm∙ Γ∙ A∙ a}{B b}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}
       {b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}{Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
     → (_,∙_ {B∙ = B∙} a∙ b∙) [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ ,[] ] (_,∙_ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (a∙ [ γ∙ ]t∙) (coe (cong Tm∙ₑ $ refl $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ $ coh) (b∙ [ γ∙ ]t∙)))
,[]∙ {A} {A∙} {a∙} {b} {B∙} {b∙} {Δ} {γ} {γ∙} = cong mkTm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ ,[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,ₚ ≈A[γ∘δ]T) = ∣ A∙ ∣ γ∘δ
    γ∘δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ ≈A[γ∘δ]T) $ refl) (γ∘δ ⁺)
    (b[γ∘δ]t ,ₚ ≈b[γ∘δ]t) = ∣ b∙ ∣ γ∘δ
    (b[γ][δ]t ,ₚ ≈b[γ][δ]t) = ∣ coe (cong Tm∙ₑ $ refl $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ A∙ B∙ a∙ γ∙ $ coh {e = cong (Tm Δ) $ [⟨⟩][]T}) (b∙ [ γ∙ ]t∙) ∣ δ
  in Σ-extₚ
       (cong ,ₑ $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)) $ refl $ (sym coh ∙ sym ≈b[γ∘δ]t ∙ cong (b [_]t) $ sym ≈γ∘δ ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ [⟨⟩][]T $ coh $ refl ∙ ≈b[γ][δ]t ∙ coh))
       (funextₕ (cong (Tm Θ) $ (cong Σ $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh))))
                λ e → cong ~ₑ $ (cong (Tm Θ) $ (cong _[ δ ]T $ Σ[])) $ (cong []tₑ $ refl $ refl $ Σ[] $ ,[] $ refl) $ (cong (Tm Θ) $ (cong Σ $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)))) $ e)

fst∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a} → Tm∙ Γ∙ (Σ∙ A∙ B∙) a → Tm∙ Γ∙ A∙ (fst a)
fst∙ {A∙} {B∙} a∙ = Tm∙.constructor λ {Δ} γ →
  let
    (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
    (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
    (B[γ⁺]T ,ₚ ≈B[γ⁺]T) = ∣ B∙ ∣ γ⁺
  in fst a[γ]t ,ₚ fst[] ∙ cong fstₑ $ refl $ ≈A[γ]T $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh ∙ ≈B[γ⁺]T) $ (sym coh ∙ ≈a[γ]t)

snd∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a}(a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a) → Tm∙ Γ∙ (B∙ [ ⟨ fst∙ {A∙ = A∙} {B∙ = B∙} a∙ ⟩∙ ]T∙) (snd a)
snd∙ {A∙} {B∙} a∙ = Tm∙.constructor λ {Δ} γ →
  let
    (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
    (a[γ]t ,ₚ ≈a[γ]t) = ∣ a∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
    (B[γ⁺]T ,ₚ ≈B[γ⁺]T) = ∣ B∙ ∣ γ⁺
    (B[γ⁺∘⟨⟩]T ,ₚ ≈B[γ⁺∘⟨⟩]T) = ∣ B∙ ∣ (γ⁺ ∘ ⟨ fst a[γ]t ⟩)
  in coe (cong (Tm Δ) $ (cong _[ ⟨ fst a[γ]t ⟩ ]T $ sym ≈B[γ⁺]T ∙ sym [∘]T ∙ ≈B[γ⁺∘⟨⟩]T)) (snd a[γ]t)
  ,ₚ snd[] ∙ cong sndₑ $ refl $ ≈A[γ]T $ (cong []Tₑ $ refl $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl $ coh ∙ ≈B[γ⁺]T) $ (sym coh ∙ ≈a[γ]t) ∙ coh

Σβ₁∙ : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ Γ∙ A}{a}{a∙ : Tm∙ Γ∙ A∙ a}{B b}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
     → fst∙ {B∙ = B∙} (_,∙_ {B∙ = B∙} a∙ b∙) ~[ cong (Tm∙ _ _) $ Σβ₁ ] a∙
Σβ₁∙ {A∙} {a∙} = cong mkTm∙ $ refl $ Σβ₁ $ funext λ {Δ} → funext λ {γ} →
  Σ-extₚ Σβ₁ (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Σβ₁) $ refl $ refl))

Σβ₂∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A a B b}{A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
     → snd∙ {A∙ = A∙} {B∙ = B∙} (_,∙_ {B∙ = B∙} a∙ b∙)
         ~[ cong (Tm∙ₑ _) $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ refl $ (cong ([]T∙ₑ Γ (Γ ▹ A) B Γ∙ (Γ∙ ▹∙ A∙) B∙) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ A∙) $ Σβ₁ $ Σβ₁∙ {a∙ = a∙} {B∙ = B∙} {b∙ = b∙})) $ Σβ₂ ]
       b∙
Σβ₂∙ {Γ} {Γ∙} {A} {a} {B} {b} {A∙} {a∙} {B∙} {b∙} = cong mkTm∙ₑ
  $ refl
  $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁)
  $ refl
  $ (cong ([]T∙ₑ Γ (Γ ▹ A) B Γ∙ (Γ∙ ▹∙ A∙) B∙) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ A∙) $ Σβ₁ $ Σβ₁∙ {a∙ = a∙} {B∙ = B∙} {b∙ = b∙}))
  $ Σβ₂
  $ funext λ {Δ} → funext λ {γ} →
    let
      (A[γ]T ,ₚ ≈A[γ]T) = ∣ A∙ ∣ γ
      γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺)
    in Σ-extₚ
         (sym coh ∙ Σβ₂ ∙ sym coh)
         (funextₕ (cong (Tm Δ) $ (cong (λ y → L.fst (∣ B∙ ∣ (γ⁺ ∘ ⟨ y ⟩))) $ Σβ₁))
                  λ e → cong ~ₑ $ (cong (λ x → Tm Δ (B [ ⟨ x ⟩ ]T [ γ ]T)) $ Σβ₁) $ (cong []tₑ $ refl $ refl $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ Σβ₂ $ refl) $ (cong (Tm Δ) $ (cong (λ y → L.fst (∣ B∙ ∣ (coe (cong Sub $ (cong (Δ ▹_) $ ≈A[γ]T) $ refl) (γ ⁺) ∘ ⟨ y ⟩))) $ Σβ₁)) $ e)

Ση∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A}{A∙ : Ty∙ Γ∙ A}{B}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a}{a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a}
    → a∙ ~[ cong (Tm∙ _ _ ) $ Ση ] (_,∙_ {A∙ = A∙} {B∙ = B∙} (fst∙ {B∙ = B∙} a∙) (snd∙ {A∙ = A∙} {B∙ = B∙} a∙))
Ση∙ = cong mkTm∙ $ refl $ Ση $ funext λ {Δ} → funext λ {γ} →
  Σ-extₚ (Ση ∙ cong _,_ $ refl $ (coh ∙ coh)) (funext (cong ~ₑ $ refl $ (cong _[ γ ]t $ Ση) $ refl $ refl))

-------- ⊤ Σ extra stuff --------

tt[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
      → tt∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) $ ⊤[] $ reflₑ Δ∙ $ ⊤[]∙ {γ∙ = γ∙} $ tt[] ] tt∙
tt[]∙ {γ∙ = γ∙} = coh ∙ ⊤η∙ {a∙ = coe (cong Tm∙ₑ $ refl $ ⊤[] $ refl $ ⊤[]∙ {γ∙ = γ∙} $ tt[]) (tt∙ [ γ∙ ]t∙)}

fst∙ₑ = λ Γ Γ∙ A A∙ B B∙ a a∙ → fst∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {a} a∙
 
fst[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B a}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a}{Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → fst∙ {A∙ = A∙} {B∙ = B∙} a∙ [ γ∙ ]t∙
           ~[ cong (Tm∙ _ _) $ fst[] ]
         fst∙ {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (coe (cong Tm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
fst[]∙ {A} {A∙} {B∙} {a∙} {γ∙} = cong mkTm∙ $ refl $ fst[] $ funext λ {Θ} → funext λ {δ} →
  let
    (γ∘δ ,ₚ ≈γ∘δ) = ∣ γ∙ ∣ δ
    (A[γ∘δ]T ,ₚ ≈A[γ∘δ]T) = ∣ A∙ ∣ γ∘δ
    (a[γ∘δ]t ,ₚ ≈a[γ∘δ]t) = ∣ a∙ ∣ γ∘δ
    (a[γ][δ]t ,ₚ ≈a[γ][δ]t) = ∣ coe (cong Tm∙ₑ $ refl $ Σ[] $ refl $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙) ∣ δ
  in Σ-extₚ
       (cong fstₑ $ refl $ refl $ (cong (λ x y → L.fst (∣ B∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym ≈γ∘δ ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ refl $ (cong (Θ ▹_) $ (sym [∘]T ∙ cong (A [_]T) $ ≈γ∘δ ∙ ≈A[γ∘δ]T)) $ refl $ coh)) $ (sym ≈a[γ∘δ]t ∙ cong []tₑ $ refl $ refl $ refl $ refl $ sym ≈γ∘δ ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ Σ[] $ coh $ refl ∙ ≈a[γ][δ]t))
       (funext (cong ~ₑ $ refl $ (cong []tₑ $ refl $ refl $ refl $ fst[] $ refl) $ refl $ refl))

snd∙ₑ = λ Γ Γ∙ A A∙ B B∙ b b∙ → snd∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {b} b∙

snd[]∙ : ∀{Γ}{Γ∙ : Con∙ Γ}{A B a}{A∙ : Ty∙ Γ∙ A}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{a∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a}
         {Δ γ}{Δ∙ : Con∙ Δ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
       → snd∙ {A∙ = A∙} {B∙ = B∙} a∙ [ γ∙ ]t∙
           ~[ cong (Tm∙ₑ _) $ ([⟨⟩][]T ∙ cong (λ x → B [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) $ refl $ ([⟨⟩][]T∙ A∙ B∙ (fst∙ {B∙ = B∙} a∙) γ∙ ∙ cong ([]T∙ₑ _ _ _ _ _ (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)) $ (cong ⟨_⟩ $ fst[]) $ (cong (⟨⟩∙ₑ _ _ _ _) $ fst[] $ fst[]∙ {A∙ = A∙} {B∙ = B∙} {a∙ = a∙} {γ∙ = γ∙} )) $ snd[] ]
         snd∙ {A∙ = A∙ [ γ∙ ]T∙} {B∙ = B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} (coe (cong Tm∙ₑ $ reflₑ Δ $ Σ[] $ reflₑ Δ∙ $ Σ[]∙ {A∙ = A∙} {B∙ = B∙} {γ∙ = γ∙} $ coh) (a∙ [ γ∙ ]t∙))
snd[]∙ {A} {B} {a} {A∙} {B∙} {a∙} {γ} {γ∙} =
  let
    (A[γ]T ,-) = ∣ A∙ ∣ γ
  in sym (cong snd∙ₑ
            $ refl
            $ refl
            $ refl
            $ reflₑ (A∙ [ γ∙ ]T∙)
            $ refl
            $ reflₑ (B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙)
            $ (sym coh ∙ cong _[ γ ]t $ Ση ∙ ,[])
            $ (sym coh ∙ cong ([]t∙ₑ _ _ _ _)
                           $ Ση
                           $ refl
                           $ refl
                           $ refl
                           $ Ση∙ {A∙ = A∙} {B∙ = B∙} {a∙ = a∙}
                           $ reflₑ γ∙ ∙ ,[]∙ {A∙ = A∙} {a∙ = fst∙ {B∙ = B∙} a∙} {B∙ = B∙} {b∙ = snd∙ {A∙ = A∙} {B∙ = B∙} a∙} {γ∙ = γ∙}) ∙ Σβ₂∙ {A = A [ γ ]T} {fst a [ γ ]t} {B [ γ ⁺ ]T} {coe (cong (Tm _) $ [⟨⟩][]T) (snd a [ γ ]t)} {A∙ [ γ∙ ]T∙} {fst∙ {A∙ = A∙} {B∙ = B∙} a∙ [ γ∙ ]t∙} {B∙ [ _⁺∙ {A∙ = A∙} γ∙ ]T∙} {coe (cong Tm∙ₑ $ refl $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ A∙ B∙ (fst∙ {B∙ = B∙} a∙) γ∙ $ coh) (snd∙ {A∙ = A∙} {B∙ = B∙} a∙ [ γ∙ ]t∙)} ∙ sym coh)
