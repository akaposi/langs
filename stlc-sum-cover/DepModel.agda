{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)

open import stlc-sum-cover.Model
import stlc-sum-cover.Syntax as I 


module stlc-sum-cover.DepModel (M : Model {lzero}{lzero}) where

module M = Model M

private variable
--   n : Nat
  Γˢ Δˢ : M.Con 
  γˢ γ₁ˢ γ₂ˢ δˢ θˢ : M.Sub Δˢ Γˢ
  Aˢ Bˢ Cˢ : M.Ty
  aˢ a₁ˢ a₂ˢ bˢ cˢ fˢ tˢ : M.Tm Γˢ Aˢ

record DepModel {ℓ}{ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  -- no-eta-equality
  field
    Con∙ : M.Con → Type ℓ
    Sub∙ : Con∙ Δˢ → Con∙ Γˢ → M.Sub Δˢ Γˢ → Type ℓ'
    SubSet∙ : ∀ {Δ Γ} → isSet (Sub∙ Δ Γ γˢ)
 
  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : ∀ {Δ Γ} → Sub∙ Δ Γ γ₁ˢ → γ₁ˢ ≡ γ₂ˢ → Sub∙ Δ Γ γ₂ˢ → Type ℓ'
  _≡ˢ[_]_ {_} {_} {_} {_} {Δ} {Γ} γ₁ γ₁ˢ≡γ₂ˢ γ₂ =
    PathP (λ i → Sub∙ Δ Γ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂

  infixl 40 _∘∙_
  field
    _∘∙_ : ∀ {Γ Δ Θ} → Sub∙ Δ Γ γˢ → Sub∙ Θ Δ δˢ → Sub∙ Θ Γ (γˢ M.∘ δˢ)
    assoc∙ :
      ∀ {Γ Δ Θ Ξ} (γ : Sub∙ Δ Γ γˢ) (δ : Sub∙ Θ Δ δˢ) (θ : Sub∙ Ξ Θ θˢ) → 
      γ ∘∙ (δ ∘∙ θ) ≡ˢ[ M.assoc γˢ δˢ θˢ ] γ ∘∙ δ ∘∙ θ

    id∙ : {Γ : Con∙ Γˢ} → Sub∙ Γ Γ M.id
    idr∙ : ∀ {Γ Δ} (γ : Sub∙ Δ Γ γˢ) → γ ∘∙ id∙ ≡ˢ[ M.idr γˢ ] γ
    idl∙ : ∀ {Γ Δ} (γ : Sub∙ Δ Γ γˢ) → id∙ ∘∙ γ ≡ˢ[ M.idl γˢ ] γ

  field
    Ty∙ : M.Ty → Type ℓ
    Tm∙ : Con∙ Γˢ → Ty∙ Aˢ → M.Tm Γˢ Aˢ → Type ℓ'
    TmSet∙ : ∀ {Γ A} → isSet (Tm∙ Γ A aˢ)

  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ A} → Tm∙ Γ A a₁ˢ → a₁ˢ ≡ a₂ˢ → Tm∙ Γ A a₂ˢ → Type ℓ'
  _≡ᵗ[_]_ {_} {_} {_} {_} {Γ} {A} a₁ a₁ˢ≡a₂ˢ a₂ =
    PathP (λ i → Tm∙ Γ A (a₁ˢ≡a₂ˢ i)) a₁ a₂

  infixl 40 _[_]∙
  field
    _[_]∙ : ∀ {Γ Δ A} → Tm∙ Γ A aˢ → Sub∙ Δ Γ γˢ → Tm∙ Δ A (aˢ M.[ γˢ ])
    []-∘∙ :
      ∀ {Γ Δ Θ A} (a : Tm∙ Γ A aˢ) (γ : Sub∙ Δ Γ γˢ) (δ : Sub∙ Θ Δ δˢ) →
      a [ γ ∘∙ δ ]∙ ≡ᵗ[ M.[]-∘ aˢ γˢ δˢ ] a [ γ ]∙ [ δ ]∙
    []-id∙ : ∀ {Γ A} (a : Tm∙ Γ A aˢ) → a [ id∙ ]∙ ≡ᵗ[ M.[]-id aˢ ] a

  infixl 4 _▸∙_ _,∙_
  field
    _▸∙_ : Con∙ Γˢ → Ty∙ Aˢ → Con∙ (Γˢ M.▸ Aˢ)
    p∙ : {Γ : Con∙ Γˢ} {A : Ty∙ Aˢ} → Sub∙ (Γ ▸∙ A) Γ M.p
    q∙ : {Γ : Con∙ Γˢ} {A : Ty∙ Aˢ} → Tm∙ (Γ ▸∙ A) A M.q

    _,∙_ : ∀ {Γ Δ A} → Sub∙ Δ Γ γˢ → Tm∙ Δ A aˢ → Sub∙ Δ (Γ ▸∙ A) (γˢ M., aˢ)
    ,-∘∙ :
      ∀ {Γ Δ Θ A} (γ : Sub∙ Δ Γ γˢ) (a : Tm∙ Δ A aˢ) (δ : Sub∙ Θ Δ δˢ) → (γ ,∙ a) ∘∙ δ ≡ˢ[ M.,-∘ γˢ aˢ δˢ ] (γ ∘∙ δ ,∙ a [ δ ]∙)
     
     
    ▸-β₁∙ :
      ∀ {Γ Δ A} (γ : Sub∙ Δ Γ γˢ) (a : Tm∙ Δ A aˢ) →
      p∙ ∘∙ (γ ,∙ a) ≡ˢ[ M.▸-β₁ γˢ aˢ ] γ
    ▸-β₂∙ :
      ∀ {Γ Δ A} (γ : Sub∙ Δ Γ γˢ) (a : Tm∙ Δ A aˢ) →
      q∙ [ γ ,∙ a ]∙ ≡ᵗ[ M.▸-β₂ γˢ aˢ ] a
    ▸-η∙ : {Γ : Con∙ Γˢ} {A : Ty∙ Aˢ} → (p∙ ,∙ q∙) ≡ˢ[ M.▸-η ] id∙ {Γ = Γ ▸∙ A}

    ◆∙ : Con∙ M.◆
    ε∙ : {Γ : Con∙ Γˢ} → Sub∙ Γ ◆∙ M.ε
    ε-∘∙ : ∀ {Γ Δ} (γ : Sub∙ Δ Γ γˢ) → ε∙ ∘∙ γ ≡ˢ[ M.ε-∘ γˢ ] ε∙
    ◆-η∙ : ε∙ ≡ˢ[ M.◆-η ] id∙

  infixl 4 _↑
  _↑ : ∀ {Γ Δ} {A : Ty∙ Aˢ} → Sub∙ Δ Γ γˢ → Sub∙ (Δ ▸∙ A) (Γ ▸∙ A) (γˢ M.↑)
  γ ↑ = γ ∘∙ p∙ ,∙ q∙

  ⟨_⟩ : ∀ {Γ A} → Tm∙ Γ A aˢ → Sub∙ Γ (Γ ▸∙ A) M.⟨ aˢ ⟩
  ⟨_⟩ = id∙ ,∙_

  infixr 0 _⇒∙_
  field
    _⇒∙_ : Ty∙ Aˢ → Ty∙ Bˢ → Ty∙ (Aˢ M.⇒ Bˢ)
    app∙ : ∀ {Γ A B} → Tm∙ Γ (A ⇒∙ B) fˢ → Tm∙ Γ A aˢ → Tm∙ Γ B (M.app fˢ aˢ)
    app-[]∙ :
      ∀ {Γ Δ A B} (f : Tm∙ Γ (A ⇒∙ B) fˢ) (a : Tm∙ Γ A aˢ) (γ : Sub∙ Δ Γ γˢ) →
      app∙ f a [ γ ]∙ ≡ᵗ[ M.app-[] fˢ aˢ γˢ ] app∙ (f [ γ ]∙) (a [ γ ]∙)

    lam∙ : ∀ {Γ A B} → Tm∙ (Γ ▸∙ A) B bˢ → Tm∙ Γ (A ⇒∙ B) (M.lam bˢ)
    lam-[]∙ :
      ∀ {Γ Δ A B} (b : Tm∙ (Γ ▸∙ A) B bˢ) (γ : Sub∙ Δ Γ γˢ) →
      lam∙ b [ γ ]∙ ≡ᵗ[ M.lam-[] bˢ γˢ ] lam∙ (b [ γ ↑ ]∙)

    ⇒-β∙ :
      ∀ {Γ A B} (b : Tm∙ (Γ ▸∙ A) B bˢ) (a : Tm∙ Γ A aˢ) →
      app∙ (lam∙ b) a ≡ᵗ[ M.⇒-β bˢ aˢ ] b [ ⟨ a ⟩ ]∙
    ⇒-η∙ :
      ∀ {Γ A B} (f : Tm∙ Γ (A ⇒∙ B) fˢ) → lam∙ (app∙ (f [ p∙ ]∙) q∙) ≡ᵗ[ M.⇒-η fˢ ] f

    ⊥ₗ∙ : Ty∙ M.⊥ₗ

    exfalsoₗ∙ : ∀ {Γ} {A : Ty∙ Aˢ} → Tm∙ Γ ⊥ₗ∙ tˢ → Tm∙ Γ A (M.exfalsoₗ tˢ)
    exfalsoₗ-[]∙ :
      ∀ {Γ Δ} {A : Ty∙ Aˢ} (t : Tm∙ Γ ⊥ₗ∙ tˢ) (γ : Sub∙ Δ Γ γˢ) → exfalsoₗ∙ {A = A} t [ γ ]∙ ≡ᵗ[ M.exfalsoₗ-[] _ _ ] exfalsoₗ∙ (t [ γ ]∙)

    ⊥ₗ-η∙ : 
      ∀ {Γ} (t : Tm∙ Γ ⊥ₗ∙ tˢ) → 
      t ≡ᵗ[ M.⊥ₗ-η tˢ ] exfalsoₗ∙ {A = ⊥ₗ∙} t

    π-⇒0∙ : 
      ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} (t : Tm∙ Γ ⊥ₗ∙ tˢ) (a : Tm∙ Γ A aˢ) → 
      app∙ (exfalsoₗ∙ {A = A ⇒∙ B} t) a ≡ᵗ[ M.π-⇒0 {B = Bˢ} tˢ aˢ ] exfalsoₗ∙ {A = B} t

    _+∙_ : Ty∙ Aˢ → Ty∙ Bˢ → Ty∙ (Aˢ M.+ Bˢ)
    inl∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} → Tm∙ Γ A aˢ → Tm∙ Γ (A +∙ B) (M.inl aˢ)
    inr∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} → Tm∙ Γ B bˢ → Tm∙ Γ (A +∙ B) (M.inr bˢ)
    caseₗ∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ} 
           → Tm∙ Γ (A +∙ B) aˢ → Tm∙ (Γ ▸∙ A) C bˢ → Tm∙ (Γ ▸∙ B) C cˢ → Tm∙ Γ C (M.caseₗ aˢ bˢ cˢ)

    inl-[]∙ : ∀ {Γ Δ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} (a : Tm∙ Γ A aˢ) (γ : Sub∙ Δ Γ γˢ)
            → inl∙ {B = B} a [ γ ]∙ ≡ᵗ[ M.inl-[] aˢ γˢ ] inl∙ (a [ γ ]∙)
    inr-[]∙ : ∀ {Γ Δ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} (b : Tm∙ Γ B bˢ) (γ : Sub∙ Δ Γ γˢ)
            → inr∙ {A = A} b [ γ ]∙ ≡ᵗ[ M.inr-[] bˢ γˢ ] inr∙ (b [ γ ]∙)
    caseₗ-[]∙ : ∀ {Γ Δ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ}
              (s : Tm∙ Γ (A +∙ B) aˢ) (l : Tm∙ (Γ ▸∙ A) C bˢ) (r : Tm∙ (Γ ▸∙ B) C cˢ) (γ : Sub∙ Δ Γ γˢ)
            → caseₗ∙ s l r [ γ ]∙ ≡ᵗ[ M.caseₗ-[] aˢ bˢ cˢ γˢ ] caseₗ∙ (s [ γ ]∙) (l [ γ ↑ ]∙) (r [ γ ↑ ]∙)

    +-β₁∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ}
           (a : Tm∙ Γ A aˢ) (l : Tm∙ (Γ ▸∙ A) C bˢ) (r : Tm∙ (Γ ▸∙ B) C cˢ)
         → caseₗ∙ (inl∙ a) l r ≡ᵗ[ M.+-β₁ aˢ bˢ cˢ ] l [ ⟨ a ⟩ ]∙
    +-β₂∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ}
           (b : Tm∙ Γ B bˢ) (l : Tm∙ (Γ ▸∙ A) C aˢ) (r : Tm∙ (Γ ▸∙ B) C cˢ)
         → caseₗ∙ (inr∙ b) l r ≡ᵗ[ M.+-β₂ bˢ aˢ cˢ ] r [ ⟨ b ⟩ ]∙

    +-η∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} (s : Tm∙ Γ (A +∙ B) aˢ)
         → caseₗ∙ s (inl∙ q∙) (inr∙ q∙) ≡ᵗ[ M.+-η aˢ ] s

    π-+⇒∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ} {D : Ty∙ _}
           (s : Tm∙ Γ (A +∙ B) aˢ) (l : Tm∙ (Γ ▸∙ A) (C ⇒∙ D) bˢ) (r : Tm∙ (Γ ▸∙ B) (C ⇒∙ D) cˢ) (u : Tm∙ Γ C fˢ)
         → app∙ (caseₗ∙ s l r) u ≡ᵗ[ M.π-+⇒ aˢ bˢ cˢ fˢ ] caseₗ∙ s (app∙ l (u [ p∙ ]∙)) (app∙ r (u [ p∙ ]∙))
    π-+0∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ}
           (s : Tm∙ Γ (A +∙ B) aˢ) (l : Tm∙ (Γ ▸∙ A) ⊥ₗ∙ bˢ) (r : Tm∙ (Γ ▸∙ B) ⊥ₗ∙ cˢ)
         → exfalsoₗ∙ {A = C} (caseₗ∙ s l r) ≡ᵗ[ M.π-+0 aˢ bˢ cˢ ] caseₗ∙ s (exfalsoₗ∙ l) (exfalsoₗ∙ r)
    π-++∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ} {D : Ty∙ _} {E : Ty∙ _}
           (s : Tm∙ Γ (A +∙ B) aˢ) (l₁ : Tm∙ (Γ ▸∙ A) (C +∙ D) bˢ) (r₁ : Tm∙ (Γ ▸∙ B) (C +∙ D) cˢ)
           (l₂ : Tm∙ (Γ ▸∙ C) E fˢ) (r₂ : Tm∙ (Γ ▸∙ D) E tˢ)
         → caseₗ∙ (caseₗ∙ s l₁ r₁) l₂ r₂ ≡ᵗ[ M.π-++ aˢ bˢ cˢ fˢ tˢ ] caseₗ∙ s (caseₗ∙ l₁ (l₂ [ p∙ ↑ ]∙) (r₂ [ p∙ ↑ ]∙)) (caseₗ∙ r₁ (l₂ [ p∙ ↑ ]∙) (r₂ [ p∙ ↑ ]∙))
    π-⇒+∙ : ∀ {Γ} {A : Ty∙ Aˢ} {B : Ty∙ Bˢ} {C : Ty∙ Cˢ}
           (t : Tm∙ Γ ⊥ₗ∙ tˢ) (l : Tm∙ (Γ ▸∙ A) C aˢ) (r : Tm∙ (Γ ▸∙ B) C bˢ)
         → caseₗ∙ (exfalsoₗ∙ {A = A +∙ B} t) l r ≡ᵗ[ M.π-⇒+ tˢ aˢ bˢ ] exfalsoₗ∙ {A = C} t