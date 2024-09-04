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

import typed-sk.Syntax as I
import typed-sk.DepModel as D

module typed-sk.Norm where


data Nf : (T : I.Ty) → I.Tm T → Type 
  
data Nf where
  K₀ : ∀{A B} → Nf (A I.⇒ (B I.⇒ A)) I.K 
  K₁ : ∀{A B t} → Nf A t → Nf (B I.⇒ A) (I.K I.· t) 
  S₀ : ∀{A B C} → Nf ((A I.⇒ B I.⇒ C) I.⇒ (A I.⇒ B) I.⇒ A I.⇒ C) I.S
  S₁ : ∀{A B C t} → Nf (A I.⇒ B I.⇒ C) t → Nf ((A I.⇒ B) I.⇒ A I.⇒ C) (I.S I.· t) 
  S₂ : ∀{A B C t u} → Nf (A I.⇒ B I.⇒ C) t → Nf (A I.⇒ B) u → Nf (A I.⇒ C) (I.S I.· t I.· u) 

Norm : D.DepModel
Norm = record
      { Ty∙ = {!   !}
      ; ι∙ = {!   !}
      ; _⇒∙_ = {!   !}
      ; Tm∙ = {!   !}
      ; TmSet· = {!   !}
      ; _$∙_ = {!   !}
      ; K∙ = {!   !}
      ; S∙ = {!   !}
      ; Kβ∙ = {!   !}
      ; Sβ∙ = {!   !}
      }

module Norm = D.DepModel Norm
  
-- norm : ∀{A}(t : I.Tm A) → Nf A t
-- norm {A} t = snd Norm.⟦ A ⟧T Norm.⟦ t ⟧t


K₀-cong : ∀{A₀ A₁ B₀ B₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ A₀ , I.K , K₀ {A₀}{B₀}) (A₁ I.⇒ B₁ I.⇒ A₁ , I.K , K₀ {A₁}{B₁})
K₀-cong a b = λ i → ((a i) I.⇒ (b i) I.⇒ (a i)) , (I.K , K₀)
K₀-inj₀ : ∀{A₀ A₁ B₀ B₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ A₀ , I.K , K₀ {A₀}{B₀}) (A₁ I.⇒ B₁ I.⇒ A₁ , I.K , K₀ {A₁}{B₁}) → A₀ ≡ A₁ 
K₀-inj₀ e =  I.inj⇒₁ (cong fst e) 
K₀-inj₁ : ∀{A₀ A₁ B₀ B₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ A₀ , I.K , K₀ {A₀}{B₀}) (A₁ I.⇒ B₁ I.⇒ A₁ , I.K , K₀ {A₁}{B₁}) → B₀ ≡ B₁ 
K₀-inj₁ e = I.inj⇒₁ (I.inj⇒₂ (cong fst e))

K₁-cong : ∀{A₀ A₁ B₀ B₁}{t₀ : I.Tm A₀}{t₁ : I.Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  A₀ ≡ A₁ →
  B₀ ≡ B₁ → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (B₀ I.⇒ A₀ , I.K I.· t₀ , K₁ v₀) (B₁ I.⇒ A₁ , I.K I.· t₁ , K₁ v₁)  
K₁-cong a b e = {!   !} --λ i → ((b i) I.⇒ (a i)) , ((I.K I.· {! !}) , {!   !})


S₀-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → C₀ ≡ C₁ → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀)
S₀-cong a b c = λ i → (((a i) I.⇒ (b i) I.⇒ (c i)) I.⇒ ((a i) I.⇒ (b i)) I.⇒ (a i) I.⇒ (c i)) , (I.S , S₀)
S₀-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀) →
  A₀ ≡ A₁
S₀-inj₀ e = I.inj⇒₁ (I.inj⇒₁ (cong fst e))
S₀-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀) →
  B₀ ≡ B₁
S₀-inj₁ e = I.inj⇒₁ (I.inj⇒₂ (I.inj⇒₁ (cong fst e)))
S₀-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀) →
  C₀ ≡ C₁
S₀-inj₂ e = I.inj⇒₂ (I.inj⇒₂ (I.inj⇒₁ (cong fst e)))

infix 4 _≟_ 

_≟_ : ∀{A₀ A₁ t₀ t₁}(v₀ : Nf A₀ t₀)(v₁ : Nf A₁ t₁) → Dec (Lift (_≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁)))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} with I.discreteTy A₀ A₁ 
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | yes eA with I.discreteTy B₀ B₁ 
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | yes eA | yes eB = yes (lift (K₀-cong eA eB))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | yes eA | no ne = no (λ e → ne (K₀-inj₁  (lower e)))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | no ne = no λ e → ne (K₀-inj₀ (lower e))
K₀ ≟ K₁ _ = no (λ {(lift e) → {! (cong fst e)  !}})
K₀ {A}{B} ≟ S₀ {A₁}{B₁}{C₁} = no (λ (lift e) → {! !})
K₀ ≟ S₁ v₁ = {!   !}
K₀ ≟ S₂ v₁ v₂ = {!   !}
K₁ v₀ ≟ v₁ = {!   !}
S₀ ≟ v₁ = {!   !}
S₁ v₀ ≟ v₁ = {!   !}
S₂ v₀ v₂ ≟ v₁ = {!   !}
-- discreteNf : ∀ {y₁} {y₂} {t₁} {t₂} (u : Nf y₁ t₁) (v : Nf y₂ t₂)(e : y₁ ≡ y₂)(e' : PathP (λ i → I.Tm (e i)) t₁ t₂ ) → Dec (PathP (λ i → Nf (e i) (e' i)) u v) 
-- discreteNf u v e e' = {!   !}
-- -- discreteNf K₀ K₀ e e' = yes (transport (λ i₁ →   PathP (λ j → I.Tm (I.isTySet _ _ refl refl i₁ j)) I.K I.K → PathP (λ i → Nf (e i) (e' i)) K₀ K₀) (λ x i → {!   !}) {!   !})

-- Norm : DepModel
-- Norm = record
--       { 
--           Ty∙ = λ A → Σ ( I.Tm A → hSet lzero ) λ P → {t : I.Tm A} → fst (P t) → Nf A t; 
--           ι∙ = (λ _ → ⊥ , λ {()}), λ {()};  
--           _⇒∙_ = λ {A}{B} A∙ B∙ → (λ t → (({u : I.Tm A} → fst (fst A∙ u) → fst (fst B∙ (t I.· u))) × Nf (A I.⇒ B) t ) , isSet× (isSetImplicitΠ λ u → isSet→ (snd ((fst B∙) (t I.· u)))) (Discrete→isSet λ x y → discreteNf x y refl refl)) , snd ;
--           Tm∙ =   λ f t → fst (fst f t); 
--           TmSet· = {!   !}; --λ {A} {A∙} {u} → {! !} ; --λ x y e e' → λ i i₁ → {! isSet→ !} ; 
--           _$∙_ = λ t u → fst t u;
--           K∙ = λ {A}{B}{A∙}{B∙} → 
--                   {!   !}; 
--                -- (λ {u₁} t → (λ {u₂} u → transport (cong (fst A∙) (sym (I.Kβ u₁ u₂))) t) , K₁ (snd A∙ t)) , K₀; 
--           S∙ = λ {_}{_}{_}{_}{_}{C∙} →  {!   !}; --λ {_}{_}{_}{_}{_}{C∙} → (λ {u₁} t → (λ {u₂} u → (λ {u₃} v → transport (cong (fst C∙) (sym (I.Sβ u₁ u₂ u₃))) (fst (fst t v) (fst u v))) , (S₂ (snd t) (snd u))) , S₁ (snd t)) , S₀; 
--           Kβ∙ =  λ {A}{B}{A∙}{B∙}(t)(u){t∙}{u∙} → {!   !}; --λ {A}{B}{A∙}{B∙}(t)(u){t∙}{u∙} → toPathP (substSubst⁻ (λ y →  fst A∙ y)  (I.Kβ t u) t∙); 
--           Sβ∙ = λ {A}{B}{C}{A∙}{B∙}{C∙}(t)(u)(v){t∙}{u∙}{v∙} → {!    !} --λ {A}{B}{C}{A∙}{B∙}{C∙}(t)(u)(v){t∙}{u∙}{v∙} → toPathP (substSubst⁻  (λ y → fst C∙ y) (I.Sβ t u v) (fst (fst t∙ v∙) (fst u∙ v∙)))
--         }   


-- Norm₁ : DepModel
-- Norm₁ = record
--       { 
--           Ty∙ = λ A → Σ ( I.Tm A → Set ) λ P → {t : I.Tm A} → P t → Nf A t; 
--           ι∙ = (λ _ → Lift ⊥) , λ {()}; 
--           _⇒∙_ = λ {A}{B} A∙ B∙ →  (λ t → ({u : I.Tm A} → fst A∙ u → fst B∙ (t I.· u)) × Nf (A I.⇒ B) t) , snd ;--λ {A}{B} A∙ B∙ → (λ t → ({u : I.Tm A} → fst A∙ u → fst B∙ (t I.· u)) × Nf (A I.⇒ B) t) , snd; 
--           Tm∙ = fst ; 
--           TmSet· = λ {A} {A∙} {u} → {! !} ; --λ x y e e' → λ i i₁ → {! isSet→ !} ; 
--           _$∙_ = λ t u → fst t u; 
--           K∙ = λ {A}{B}{A∙}{B∙} →
--                 (λ {u₁} t → (λ {u₂} u → transport (cong (fst A∙) (sym (I.Kβ u₁ u₂))) t) , K₁ (snd A∙ t)) , K₀; 
--           S∙ = λ {_}{_}{_}{_}{_}{C∙} → (λ {u₁} t → (λ {u₂} u → (λ {u₃} v → transport (cong (fst C∙) (sym (I.Sβ u₁ u₂ u₃))) (fst (fst t v) (fst u v))) , (S₂ (snd t) (snd u))) , S₁ (snd t)) , S₀; 
--           Kβ∙ =  λ {A}{B}{A∙}{B∙}(t)(u){t∙}{u∙} → toPathP (substSubst⁻ (λ y →  fst A∙ y)  (I.Kβ t u) t∙); 
--           Sβ∙ = λ {A}{B}{C}{A∙}{B∙}{C∙}(t)(u)(v){t∙}{u∙}{v∙} → toPathP (substSubst⁻  (λ y → fst C∙ y) (I.Sβ t u v) (fst (fst t∙ v∙) (fst u∙ v∙)))
--         }            