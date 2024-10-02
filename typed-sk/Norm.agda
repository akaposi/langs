{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Agda.Builtin.Unit
import typed-sk.Syntax as I
import typed-sk.DepModel as D
import typed-sk.NormalForm as N 

module typed-sk.Norm where

Norm : D.DepModel
Norm = record
      { 
          Ty∙ = λ A → Σ ( I.Tm A → hSet lzero ) λ P → {t : I.Tm A} → fst (P t) → N.Nf A t; 
          ι∙ = (λ _ → ⊥ , λ {()}), λ {()};  
          _⇒∙_ = λ {A}{B} A∙ B∙ → (λ t → (({u : I.Tm A} → fst (fst A∙ u) → fst (fst B∙ (t I.· u))) × N.Nf (A I.⇒ B) t ) , isSet× (isSetImplicitΠ λ u → isSet→ (snd ((fst B∙) (t I.· u)))) N.NfSet) , snd ; --discreteNf x y refl refl
          Tm∙ =   λ f t → fst (fst f t); 
          TmSet· = λ {A}{A∙}{u} → snd (fst A∙ u); 
          _$∙_ = λ t u → fst t u;
          K∙ = λ {A}{B}{A∙}{B∙} → (λ {u₁} t → (λ {u₂} u → transport   (cong (fst ∘ fst A∙) (sym (I.Kβ u₁ u₂))) t) , N.Nf.K₁ (snd A∙ t)) , N.Nf.K₀;
          S∙ = λ {_}{_}{_}{_}{_}{C∙} →  (λ {u₁} t → (λ {u₂} u → (λ {u₃} v → transport (cong (fst ∘ fst C∙) (sym (I.Sβ u₁ u₂ u₃))) ((fst (fst t v) (fst u v)))) , N.Nf.S₂ (snd t) (snd u)) , N.Nf.S₁ (snd t)) , N.Nf.S₀; 
          Kβ∙ =  λ {A}{B}{A∙}{B∙}(t)(u){t∙}{u∙} → toPathP (substSubst⁻ (λ y →  (fst ∘ fst A∙) y) (I.Kβ t u) t∙); 
          Sβ∙ = λ {A}{B}{C}{A∙}{B∙}{C∙}(t)(u)(v){t∙}{u∙}{v∙} → toPathP (substSubst⁻ (λ y → (fst ∘ fst C∙) y) (I.Sβ t u v) (fst (fst t∙ v∙) (fst u∙ v∙)))
        }
module Norm = D.DepModel Norm

norm : ∀{A}(t : I.Tm A) → N.Nf A t
norm {A} t = snd Norm.⟦ A ⟧T Norm.⟦ t ⟧t
