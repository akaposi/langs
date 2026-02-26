{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
import stlc-sum.Syntax as I

module stlc-sum.Model where

record Model {ℓ}{ℓ'} : Type (lsuc (ℓ ⊔ ℓ')) where
  -- no-eta-equality
  infixl 40 _∘_ _[_]
  infixl 4 _▸_ _,_

  field
    Con : Type ℓ
    Sub : Con → Con → Type ℓ'
    SubSet : ∀ {Δ Γ} → isSet (Sub Δ Γ)

    _∘_ : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    assoc :
      ∀ {Γ Δ Θ Ξ} (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) →
      γ ∘ (δ ∘ θ) ≡ γ ∘ δ ∘ θ

    id : ∀ {Γ} → Sub Γ Γ
    idr : ∀ {Γ Δ} (γ : Sub Δ Γ) → γ ∘ id ≡ γ
    idl : ∀ {Γ Δ} (γ : Sub Δ Γ) → id ∘ γ ≡ γ

    Ty : Type ℓ
    Tm : Con → Ty → Type ℓ'
    TmSet : ∀ {Γ A} → isSet (Tm Γ A)

    _[_] : ∀ {Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    []-∘ :
      ∀ {Γ Δ Θ A} (a : Tm Γ A) (γ : Sub Δ Γ) (δ : Sub Θ Δ) →
      a [ γ ∘ δ ] ≡ a [ γ ] [ δ ]
    []-id : ∀ {Γ A} (a : Tm Γ A) → a [ id ] ≡ a

    _▸_ : Con → Ty → Con
    p : ∀ {Γ A} → Sub (Γ ▸ A) Γ
    q : ∀ {Γ A} → Tm (Γ ▸ A) A

    _,_ : ∀ {Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▸ A)
    ,-∘ :
      ∀ {Γ Δ Θ A} (γ : Sub Δ Γ) (a : Tm Δ A) (δ : Sub Θ Δ) →
      (γ , a) ∘ δ ≡ (γ ∘ δ , a [ δ ])

    ▸-β₁ : ∀ {Γ Δ A} (γ : Sub Δ Γ) (a : Tm Δ A) → p ∘ (γ , a) ≡ γ
    ▸-β₂ : ∀ {Γ Δ A} (γ : Sub Δ Γ) (a : Tm Δ A) → q [ γ , a ] ≡ a
    ▸-η : ∀ {Γ A} → (p , q) ≡ id {Γ ▸ A}

    ◆ : Con
    ε : ∀ {Γ} → Sub Γ ◆
    ε-∘ : ∀ {Γ Δ} (γ : Sub Δ Γ) → ε ∘ γ ≡ ε
    ◆-η : ε ≡ id
    
  infixl 4 _↑
  _↑ : ∀ {Γ Δ A} → Sub Δ Γ → Sub (Δ ▸ A) (Γ ▸ A)
  γ ↑ = γ ∘ p , q

  ⟨_⟩ : ∀ {Γ A} → Tm Γ A → Sub Γ (Γ ▸ A)
  ⟨_⟩ = id ,_

  infixr 0 _⇒_
  field
    
    ⊥ₗ : Ty
    Unitₗ : Ty
    _⇒_ : Ty → Ty → Ty
    _+ₗ_ : Ty → Ty → Ty
    app : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
    app-[] :
      ∀ {Γ Δ A B} (f : Tm Γ (A ⇒ B)) a (γ : Sub Δ Γ) →
      app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

    lam : ∀ {Γ A B} → Tm (Γ ▸ A) B → Tm Γ (A ⇒ B)
    lam-[] :
      ∀ {Γ Δ A B} (b : Tm (Γ ▸ A) B) (γ : Sub Δ Γ) →
      lam b [ γ ] ≡ lam (b [ γ ↑ ])

    ⇒-β : ∀ {Γ A B} (b : Tm (Γ ▸ A) B) a → app (lam b) a ≡ b [ ⟨ a ⟩ ]
    ⇒-η : ∀ {Γ A B} (f : Tm Γ (A ⇒ B)) → lam (app (f [ p ]) q) ≡ f

    exfalsoₗ : ∀ {Γ A} → Tm Γ ⊥ₗ → Tm Γ A
    exfalsoₗ-[] : ∀ {Γ Δ A} t (γ : Sub Δ Γ) → exfalsoₗ {A = A} t [ γ ] ≡ exfalsoₗ (t [ γ ])

    ttₗ : ∀ {Γ} → Tm Γ Unitₗ
    ttₗ-[] : ∀ {Δ Γ}(γ : Sub Δ Γ) → ttₗ [ γ ] ≡ ttₗ 

    unit-η : ∀ {Γ}(t : Tm Γ Unitₗ) → t ≡ ttₗ

    inlₗ  : ∀ {Γ A B} → Tm Γ A → Tm Γ (A +ₗ B) 
    inlₗ-[] :  ∀ {Γ A B Δ} → (a : Tm Γ A)(γ : Sub Δ Γ) → inlₗ {B = B} a [ γ ] ≡ inlₗ {B = B} (a [ γ ]) 
    inrₗ  : ∀ {Γ A B} → Tm Γ B → Tm Γ (A +ₗ B)  
    inrₗ-[] : ∀ {Γ A B Δ} → (b : Tm Γ B)(γ : Sub Δ Γ) → inrₗ {A = A} b [ γ ] ≡ inrₗ {A = A} (b [ γ ]) 

    case+ : ∀ {Γ A B C} → Tm Γ (A +ₗ B) → Tm (Γ ▸ A) C → Tm (Γ ▸ B) C → Tm Γ C 
    case+[] :  ∀ {Γ A B C Δ} → (t : Tm Γ (A +ₗ B))(a :  Tm (Γ ▸ A) C)(b :  Tm (Γ ▸ B) C) (γ : Sub Δ Γ) → case+ t a b [ γ ] ≡ case+ (t [ γ ]) (a [ γ ↑ ]) (b [ γ ↑ ])

    +-β₁ : ∀ {Γ A B C} → (t : Tm Γ A) (a : Tm (Γ ▸ A) C)(b : Tm (Γ ▸ B) C) → case+ (inlₗ {B = B} t) a b ≡ a [ id , t ]
    +-β₂ : ∀ {Γ A B C} → (t : Tm Γ B) (a : Tm (Γ ▸ A) C)(b : Tm (Γ ▸ B) C) → case+ (inrₗ {A = A} t) a b ≡ b [ id , t ]

    -- +-η : ∀ {Γ A B} → (t : Tm Γ (A +ₗ B))(a : Tm (Γ ▸ A) A)(b : Tm (Γ ▸ B) B) → case+ t (inlₗ a) (inrₗ b) ≡ t 




--Recursor 

  ⟦_⟧T : I.Ty → Ty
  ⟦ I.Unitₗ ⟧T = Unitₗ
  ⟦ I.⊥ₗ ⟧T = ⊥ₗ
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T
  ⟦ A I.+ₗ B ⟧T = ⟦ A ⟧T +ₗ ⟦ B ⟧T

  ⟦_⟧C : I.Con → Con
  ⟦ Γ I.▸ A ⟧C = ⟦ Γ ⟧C ▸ ⟦ A ⟧T
  ⟦ I.◆ ⟧C = ◆

  ⟦_⟧S : ∀ {Γ Δ} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C ⟦ Γ ⟧C 
  ⟦_⟧t : ∀ {Γ A} → I.Tm Γ A → Tm ⟦ Γ ⟧C ⟦ A ⟧T 
  
  ⟦ I.SubSet γ₁ γ₂ p q i j ⟧S = SubSet _ _ (λ k → ⟦ (p k) ⟧S) (λ k → ⟦ (q k) ⟧S) i j
  ⟦ γ I.∘ δ ⟧S = ⟦ γ ⟧S ∘ ⟦ δ ⟧S
  ⟦ I.assoc γ δ θ i ⟧S = assoc ⟦ γ ⟧S ⟦ δ ⟧S ⟦ θ ⟧S i
  ⟦ I.id ⟧S = id
  ⟦ I.idr γ i ⟧S = idr ⟦ γ ⟧S i
  ⟦ I.idl γ i ⟧S = idl ⟦ γ ⟧S i
  ⟦ I.p ⟧S = p
  ⟦ γ I., a ⟧S = ⟦ γ ⟧S , ⟦ a ⟧t
  ⟦ I.,-∘ γ a δ i ⟧S = ,-∘ ⟦ γ ⟧S ⟦ a ⟧t ⟦ δ ⟧S i
  ⟦ I.▸-β₁ γ a i ⟧S = ▸-β₁ ⟦ γ ⟧S ⟦ a ⟧t i
  ⟦ I.▸-η i ⟧S = ▸-η i
  ⟦ I.ε ⟧S = ε
  ⟦ I.ε-∘ γ i ⟧S = ε-∘ ⟦ γ ⟧S i
  ⟦ I.◆-η i ⟧S = ◆-η i

  ⟦ I.TmSet a₁ a₂ p q i j ⟧t = TmSet _ _ (λ k → ⟦ (p k) ⟧t) (λ k → ⟦ (q k) ⟧t) i j
  ⟦ a I.[ γ ] ⟧t = ⟦ a ⟧t [ ⟦ γ ⟧S ]
  ⟦ I.[]-∘ a γ δ i ⟧t = []-∘ ⟦ a ⟧t ⟦ γ ⟧S ⟦ δ ⟧S i
  ⟦ I.[]-id a i ⟧t = []-id ⟦ a ⟧t i
  ⟦ I.q ⟧t = q
  ⟦ I.▸-β₂ γ a i ⟧t = ▸-β₂ ⟦ γ ⟧S ⟦ a ⟧t i
  ⟦ I.app f a ⟧t = app ⟦ f ⟧t ⟦ a ⟧t
  ⟦ I.app-[] f a γ i ⟧t = app-[] ⟦ f ⟧t ⟦ a ⟧t ⟦ γ ⟧S i
  ⟦ I.lam a ⟧t = lam ⟦ a ⟧t
  ⟦ I.lam-[] a γ i ⟧t = lam-[] ⟦ a ⟧t ⟦ γ ⟧S i
  ⟦ I.⇒-β f a i ⟧t = ⇒-β ⟦ f ⟧t ⟦ a ⟧t i
  ⟦ I.⇒-η a i ⟧t = ⇒-η ⟦ a ⟧t i
  ⟦ I.exfalsoₗ t ⟧t = exfalsoₗ ⟦ t ⟧t
  ⟦ I.exfalsoₗ-[] t γ i ⟧t = exfalsoₗ-[] ⟦ t ⟧t ⟦ γ ⟧S i
  ⟦ I.ttₗ ⟧t = ttₗ
  ⟦ I.ttₗ-[] γ i ⟧t = ttₗ-[] ⟦ γ ⟧S i
  ⟦ I.unit-η t i ⟧t = unit-η ⟦ t ⟧t i
  ⟦ I.inlₗ a ⟧t = inlₗ ⟦ a ⟧t
  ⟦ I.inlₗ-[] a γ i ⟧t = inlₗ-[] ⟦ a ⟧t ⟦ γ ⟧S i
  ⟦ I.inrₗ a ⟧t = inrₗ ⟦ a ⟧t
  ⟦ I.inrₗ-[] a γ i ⟧t = inrₗ-[] ⟦ a ⟧t ⟦ γ ⟧S i
  ⟦ I.case+ t a b ⟧t = case+ ⟦ t ⟧t ⟦ a ⟧t ⟦ b ⟧t
  ⟦ I.case+[] t a b γ i ⟧t = case+[] ⟦ t ⟧t ⟦ a ⟧t ⟦ b ⟧t ⟦ γ ⟧S i
  ⟦ I.+-β₁ t a b i ⟧t = +-β₁ ⟦ t ⟧t ⟦ a ⟧t ⟦ b ⟧t i
  ⟦ I.+-β₂ t a b i ⟧t = +-β₂ ⟦ t ⟧t ⟦ a ⟧t ⟦ b ⟧t i


    -- ⟦ I.+-η t a b i ⟧t = +-η ⟦ t ⟧t ⟦ a ⟧t ⟦ b ⟧t i


