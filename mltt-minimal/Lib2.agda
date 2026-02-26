{-# OPTIONS --cubical  #-} ----guardedness
{-# OPTIONS --allow-unsolved-metas #-} 
open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Equality renaming (funExt to IndfunExt; _≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ; ap to Indap) hiding (isProp)
open import Cubical.Foundations.Path
open import mltt-minimal.Syntax

-- open import Cubical.Data.Equality.Conversion 
module mltt-minimal.Lib2 where

data UU : Type
ElU : UU → Type


data UU where
  ConU : UU
  SubU :  Con → Con → UU
  TyU :  Con → UU
  TmU : (Γ : Con) → Ty Γ  → UU
  PathU : {A₁ : UU} → ElU A₁ → ElU A₁ → UU
  ΠU  : (a : UU)(b : ElU a → UU) → UU 
  ΣU  : (a : UU)(b : ElU a → UU) → UU
  ⊥U  : UU

ElU ConU = Con
ElU (SubU Δ Γ) = Sub Δ Γ
ElU (TyU Γ) = Ty Γ
ElU (TmU Γ A) = Tm Γ A
ElU (PathU p1 p2) = p1 ≡ p2
ElU (ΠU a b) = (x : ElU a) → ElU (b x)
ElU (ΣU a b) = Σ (ElU a) λ x → ElU (b x)
ElU ⊥U = ⊥

isSetUU : isSet UU
isSetUU A A' = {!   !}

isSetElU : (u : UU) → isSet (ElU u)
isSetElU = {!   !}
