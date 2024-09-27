{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to exfalso) 
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
module stlc-minimal.InitialModel where

import stlc-minimal.Model as Mod

open import stlc-minimal.Syntax

In : Mod.Model
In = record
      { Con = Con
      ; Sub = {!Sub!}
      ; SubSet = {!!}
      ; _∘_ = {!!}
      ; assoc = {!!}
      ; id = {!!}
      ; idr = {!!}
      ; idl = {!!}
      ; Ty = {!!}
      ; Tm = {!!}
      ; TmSet = {!!}
      ; _[_] = {!!}
      ; []-∘ = {!!}
      ; []-id = {!!}
      ; _▸_ = {!!}
      ; p = {!!}
      ; q = {!!}
      ; _,_ = {!!}
      ; ,-∘ = {!!}
      ; ▸-β₁ = {!!}
      ; ▸-β₂ = {!!}
      ; ▸-η = {!!}
      ; ◆ = {!!}
      ; ε = {!!}
      ; ε-∘ = {!!}
      ; ◆-η = {!!}
      ; _⇒_ = {!!}
      ; app = {!!}
      ; app-[] = {!!}
      ; lam = {!!}
      ; lam-[] = {!!}
      ; ⇒-β = {!!}
      ; ⇒-η = {!!}
      ; ι = {!!}
      }

InStrict : Mod.Model
InStrict = record
      { Con = Con
      ; Sub = {!Sub!}
      ; SubSet = {!!}
      ; _∘_ = {!!}
      ; assoc = {!!}
      ; id = {!!}
      ; idr = {!!}
      ; idl = {!!}
      ; Ty = {!!}
      ; Tm = {!!}
      ; TmSet = {!!}
      ; _[_] = {!_[_]*!}
      ; []-∘ = {!!}
      ; []-id = {!!}
      ; _▸_ = {!!}
      ; p = {!!}
      ; q = {!!}
      ; _,_ = {!!}
      ; ,-∘ = {!!}
      ; ▸-β₁ = {!!}
      ; ▸-β₂ = {!!}
      ; ▸-η = {!!}
      ; ◆ = {!!}
      ; ε = {!!}
      ; ε-∘ = {!!}
      ; ◆-η = {!!}
      ; _⇒_ = {!!}
      ; app = {!!}
      ; app-[] = {!refl!}
      ; lam = {!!}
      ; lam-[] = {!refl!}
      ; ⇒-β = {!!}
      ; ⇒-η = {!!}
      ; ι = {!!}
      }
