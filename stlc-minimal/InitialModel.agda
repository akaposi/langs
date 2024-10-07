{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to exfalso) 
open import Cubical.Foundations.HLevels
module stlc-minimal.InitialModel where

import stlc-minimal.Model as Mod

open import stlc-minimal.Syntax

In : Mod.Model
In = record
      { Con = Con
      ; Sub = Sub
      ; SubSet = λ {Δ Γ} → SubSet
      ; _∘_ = λ {Δ Γ Θ} → _∘_
      ; assoc = assoc
      ; id = id
      ; idr = idr
      ; idl = idl
      ; Ty = Ty
      ; Tm = Tm
      ; TmSet = TmSet
      ; _[_] = _[_]
      ; []-∘ = []-∘
      ; []-id = []-id
      ; _▸_ = _▸_
      ; p = p
      ; q = q
      ; _,_ = _,_
      ; ,-∘ = ,-∘
      ; ▸-β₁ = ▸-β₁
      ; ▸-β₂ = ▸-β₂
      ; ▸-η = ▸-η
      ; ◆ = ◆
      ; ε = ε
      ; ε-∘ = ε-∘
      ; ◆-η = ◆-η
      ; _⇒_ = _⇒_
      ; app = app
      ; app-[] = app-[]
      ; lam = lam
      ; lam-[] = lam-[]
      ; ⇒-β = ⇒-β
      ; ⇒-η = ⇒-η
      ; ι = ι
      }

InStrict : Mod.Model
InStrict = record
      { Con = Con
      ; Sub = Sub
      ; SubSet = SubSet
      ; _∘_ = _∘_
      ; assoc =  assoc
      ; id = id
      ; idr = idr
      ; idl = idl
      ; Ty = Ty
      ; Tm = Tm
      ; TmSet = TmSet
      ; _[_] = _[_]*
      ; []-∘ = λ a γ δ → (a [ γ ∘ δ ]=) ∙ ([]-∘ a γ δ ) ∙ ((cong (_[ δ ]) (sym (a [ γ ]=)) ∙ sym ((a [ γ ]*) [ δ ]=)))
      ; []-id = λ a → (a [ id ]=) ∙ []-id a
      ; _▸_ = _▸_
      ; p = p
      ; q = q
      ; _,_ = _,_
      ; ,-∘ = λ γ a δ → (,-∘ γ a δ) ∙ cong (λ z → γ ∘ δ , z)  (sym(a [ δ ]=))
      ; ▸-β₁ = ▸-β₁
      ; ▸-β₂ = ▸-β₂
      ; ▸-η = ▸-η
      ; ◆ = ◆
      ; ε = ε
      ; ε-∘ = ε-∘
      ; ◆-η = ◆-η
      ; _⇒_ = _⇒_
      ; app = app
      ; app-[] = λ f a γ → refl
      ; lam = lam
      ; lam-[] =  λ b γ → refl
      ; ⇒-β = λ b a → (⇒-β b a) ∙ sym (b [ id , a ]=)
      ; ⇒-η = λ f → cong (λ x → lam (app x q)) (f [ p ]=) ∙ (⇒-η f)
      ; ι = ι
      }
   
