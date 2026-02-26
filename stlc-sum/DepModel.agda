{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)

open import stlc-sum.Model
import stlc-sum.Syntax as I 


module stlc-sum.DepModel (M : Model {lzero}{lzero}) where

module M = Model M

private variable
--   n : Nat
  Γˢ Δˢ : M.Con 
  γˢ γ₁ˢ γ₂ˢ δˢ θˢ : M.Sub Δˢ Γˢ
  Aˢ Bˢ : M.Ty
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
    _+ₗ∙_ : Ty∙ Aˢ → Ty∙ Bˢ → Ty∙ (Aˢ M.+ₗ Bˢ) --*
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

    Unitₗ∙ : Ty∙ M.Unitₗ
    ttₗ∙ : ∀ {Γ : Con∙ Γˢ} → Tm∙ Γ Unitₗ∙ M.ttₗ
    ttₗ-[]∙ : ∀ {Δ Γ}(γ : Sub∙ Δ Γ γˢ) → ttₗ∙ [ γ ]∙  ≡ᵗ[ M.ttₗ-[] _ ] ttₗ∙ 
    
    unit-η∙ : ∀ {Γ} (t : Tm∙ Γ Unitₗ∙ tˢ) → t ≡ᵗ[ M.unit-η tˢ ] ttₗ∙

    inlₗ∙ : ∀ {Γ A B} → Tm∙ Γ A aˢ → Tm∙ Γ (A +ₗ∙ B) (M.inlₗ {B = Bˢ} aˢ)
    inlₗ-[]∙ : ∀ {Γ A B Δ} → (a : Tm∙ Γ A aˢ)(γ : Sub∙ Δ Γ γˢ) → inlₗ∙ {B = B} a [ γ ]∙ ≡ᵗ[ M.inlₗ-[]  {B = Bˢ} aˢ γˢ ] inlₗ∙ {B = B}  (a [ γ ]∙)
    inrₗ∙ : ∀ {Γ A B} → Tm∙ Γ B bˢ → Tm∙ Γ (A +ₗ∙ B) (M.inrₗ {A = Aˢ} bˢ)
    inrₗ-[]∙ : ∀ {Γ A B Δ} → (b : Tm∙ Γ B bˢ)(γ : Sub∙ Δ Γ γˢ) → inrₗ∙ {A = A} b [ γ ]∙ ≡ᵗ[ M.inrₗ-[] {A = Aˢ} bˢ γˢ ] inrₗ∙ {A = A}  (b [ γ ]∙)  

    case+∙ :  ∀ {Γ A B C} → Tm∙ Γ (A +ₗ∙ B) cˢ → Tm∙ (Γ ▸∙ A) C aˢ → Tm∙ (Γ ▸∙ B) C bˢ → Tm∙ Γ C (M.case+ cˢ aˢ bˢ)
    case+[]∙ : ∀ {Γ A B C Δ} → (t : Tm∙ Γ (A +ₗ∙ B) cˢ)(a : Tm∙ (Γ ▸∙ A) C aˢ)(b : Tm∙ (Γ ▸∙ B) C bˢ)(γ : Sub∙ Δ Γ γˢ) → case+∙ t a b [ γ ]∙ ≡ᵗ[ M.case+[] cˢ aˢ bˢ γˢ ] case+∙ (t [ γ ]∙) (a [ γ ↑ ]∙) (b [ γ ↑ ]∙)
    
    +-β₁∙ : ∀ {Γ A B C} → (t : Tm∙ Γ A tˢ) (a : Tm∙ (Γ ▸∙ A) C aˢ)(b : Tm∙ (Γ ▸∙ B) C bˢ) → case+∙ (inlₗ∙ {B = B} t) a b ≡ᵗ[ M.+-β₁ tˢ aˢ bˢ ] (a [ id∙ ,∙ t ]∙) 
    +-β₂∙ : ∀ {Γ A B C} → (t : Tm∙ Γ B tˢ) (a : Tm∙ (Γ ▸∙ A) C aˢ)(b : Tm∙ (Γ ▸∙ B) C bˢ) → case+∙ (inrₗ∙ {A = A} t) a b ≡ᵗ[ M.+-β₂ tˢ aˢ bˢ ] (b [ id∙ ,∙ t ]∙)  

    -- +-η∙ : ∀ {Γ A B} → (t : Tm∙ Γ (A +ₗ∙ B) tˢ)(a : Tm∙ (Γ ▸∙ A) A aˢ)(b : Tm∙ (Γ ▸∙ B) B bˢ) → case+∙ t (inlₗ∙ a) (inrₗ∙ b) ≡ᵗ[ M.+-η tˢ aˢ bˢ ]  t 
    -- weak eta
