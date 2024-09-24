{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to exfalso) 
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
module stlc-minimal.StandardModel where

open import stlc-minimal.Model

St : (A : hSet lzero) → Model
St A = record
        { 
            Con = hSet lzero
            ; Sub = λ Δ Γ → fst Δ → fst Γ
            ; SubSet = λ {Δ Γ} → isSet→ (snd Γ)
            ; _∘_ = λ γ δ θ → γ (δ θ)
            ; assoc = λ γ δ θ → refl
            ; id = λ γ → γ
            ; idr = λ γ → refl
            ; idl = λ γ → refl
            ; Ty = hSet lzero
            ; Tm = λ Γ A → fst Γ → fst A
            ; TmSet = λ {Γ A} → isSet→ (snd A)
            ; _[_] = λ a γ δ → a (γ δ)
            ; []-∘ = λ a γ δ → refl
            ; []-id = λ a → refl
            ; _▸_ = λ Γ A → (fst Γ × fst A , isSet× (snd Γ) (snd A) )
            ; p = λ (γ , a) → γ
            ; q = λ (γ , a) → a
            ; _,_ = λ γ a δ → (γ δ) , a δ
            ; ,-∘ = λ γ a δ → refl
            ; ▸-β₁ = λ γ a → refl
            ; ▸-β₂ = λ γ a → refl
            ; ▸-η = refl
            ; ◆ = ⊤ , λ tt tt e e' → refl
            ; ε = λ {Γ} x → tt
            ; ε-∘ =  λ γ i a → tt
            ; ◆-η = λ i a → tt
            ; _⇒_ = λ A B → (fst A → fst B) , (isSet→ (snd B))
            ; app = λ f a γ → f γ (a γ)
            ; app-[] = λ f a γ → refl
            ; lam = λ b γ a → b (γ , a)
            ; lam-[] = λ b γ → refl
            ; ⇒-β = λ b a → refl
            ; ⇒-η = λ f → refl
            ; ι = A
            -- ; ι-rec = λ  {Γ} {A} f t → {!  !}
            -- ; ι-rec-[] = {!   !}
        }


module St⊥ = Model (St (⊥ , isProp→isSet isProp⊥))

open import stlc-minimal.Syntax

consistency : Tm ◆ ι  → ⊥
consistency t = St⊥.⟦ t ⟧t tt
   