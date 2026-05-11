{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
import stlc-sum-cover.Syntax as I

module stlc-sum-cover.Model where

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
    _⇒_ : Ty → Ty → Ty
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

    ⊥ₗ-η : ∀ {Γ} (t : Tm Γ ⊥ₗ) → t ≡ exfalsoₗ {A = ⊥ₗ} t

    π-⇒0 : ∀ {Γ A B} (t : Tm Γ ⊥ₗ) (u : Tm Γ A) 
       → app (exfalsoₗ {A = A ⇒ B} t) u ≡ exfalsoₗ {A = B} t

    _+_ : Ty → Ty → Ty
    inl : ∀ {Γ A B} → Tm Γ A → Tm Γ (A + B)
    inr : ∀ {Γ A B} → Tm Γ B → Tm Γ (A + B)
    caseₗ : ∀ {Γ A B C} → Tm Γ (A + B) → Tm (Γ ▸ A) C → Tm (Γ ▸ B) C → Tm Γ C

    inl-[] : ∀ {Γ Δ A B} (a : Tm Γ A) (γ : Sub Δ Γ) → inl {B = B} a [ γ ] ≡ inl (a [ γ ])
    inr-[] : ∀ {Γ Δ A B} (b : Tm Γ B) (γ : Sub Δ Γ) → inr {A = A} b [ γ ] ≡ inr (b [ γ ])
    caseₗ-[] : ∀ {Γ Δ A B C} (s : Tm Γ (A + B)) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C) (γ : Sub Δ Γ)
             → caseₗ s l r [ γ ] ≡ caseₗ (s [ γ ]) (l [ γ ↑ ]) (r [ γ ↑ ])

    +-β₁ : ∀ {Γ A B C} (a : Tm Γ A) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C)
         → caseₗ (inl a) l r ≡ l [ ⟨ a ⟩ ]
    +-β₂ : ∀ {Γ A B C} (b : Tm Γ B) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C)
         → caseₗ (inr b) l r ≡ r [ ⟨ b ⟩ ]

    +-η : ∀ {Γ A B} (s : Tm Γ (A + B)) → caseₗ s (inl q) (inr q) ≡ s

    π-+⇒ : ∀ {Γ A B C D} (s : Tm Γ (A + B)) (l : Tm (Γ ▸ A) (C ⇒ D)) (r : Tm (Γ ▸ B) (C ⇒ D)) (u : Tm Γ C)
         → app (caseₗ s l r) u ≡ caseₗ s (app l (u [ p ])) (app r (u [ p ]))
    π-+0 : ∀ {Γ A B C} (s : Tm Γ (A + B)) (l : Tm (Γ ▸ A) ⊥ₗ) (r : Tm (Γ ▸ B) ⊥ₗ)
         → exfalsoₗ {A = C} (caseₗ s l r) ≡ caseₗ s (exfalsoₗ l) (exfalsoₗ r)
    π-++ : ∀ {Γ A B C D E} (s : Tm Γ (A + B)) (l₁ : Tm (Γ ▸ A) (C + D)) (r₁ : Tm (Γ ▸ B) (C + D))
             (l₂ : Tm (Γ ▸ C) E) (r₂ : Tm (Γ ▸ D) E)
         → caseₗ (caseₗ s l₁ r₁) l₂ r₂ ≡ caseₗ s (caseₗ l₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) (caseₗ r₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ]))
    π-⇒+ : ∀ {Γ A B C} (t : Tm Γ ⊥ₗ) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C)
         → caseₗ (exfalsoₗ {A = A + B} t) l r ≡ exfalsoₗ {A = C} t

--Recursor 

  ⟦_⟧T : I.Ty → Ty
  ⟦ I.⊥ₗ ⟧T = ⊥ₗ
  ⟦ A I.⇒ B ⟧T = ⟦ A ⟧T ⇒ ⟦ B ⟧T
  ⟦ A I.+ B ⟧T = ⟦ A ⟧T + ⟦ B ⟧T

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
  ⟦ I.⊥ₗ-η t i ⟧t = ⊥ₗ-η ⟦ t ⟧t i
  ⟦ I.π-⇒0 b t i ⟧t = π-⇒0 ⟦ b ⟧t ⟦ t ⟧t i
  ⟦ I.inl a ⟧t = inl ⟦ a ⟧t
  ⟦ I.inr b ⟧t = inr ⟦ b ⟧t
  ⟦ I.caseₗ s l r ⟧t = caseₗ ⟦ s ⟧t ⟦ l ⟧t ⟦ r ⟧t
  ⟦ I.inl-[] a γ i ⟧t = inl-[] ⟦ a ⟧t ⟦ γ ⟧S i
  ⟦ I.inr-[] b γ i ⟧t = inr-[] ⟦ b ⟧t ⟦ γ ⟧S i
  ⟦ I.caseₗ-[] s l r γ i ⟧t = caseₗ-[] ⟦ s ⟧t ⟦ l ⟧t ⟦ r ⟧t ⟦ γ ⟧S i
  ⟦ I.+-β₁ a l r i ⟧t = +-β₁ ⟦ a ⟧t ⟦ l ⟧t ⟦ r ⟧t i
  ⟦ I.+-β₂ b l r i ⟧t = +-β₂ ⟦ b ⟧t ⟦ l ⟧t ⟦ r ⟧t i
  ⟦ I.+-η s i ⟧t = +-η ⟦ s ⟧t i
  ⟦ I.π-+⇒ s l r u i ⟧t = π-+⇒ ⟦ s ⟧t ⟦ l ⟧t ⟦ r ⟧t ⟦ u ⟧t i
  ⟦ I.π-+0 s l r i ⟧t = π-+0 ⟦ s ⟧t ⟦ l ⟧t ⟦ r ⟧t i
  ⟦ I.π-++ s l₁ r₁ l₂ r₂ i ⟧t = π-++ ⟦ s ⟧t ⟦ l₁ ⟧t ⟦ r₁ ⟧t ⟦ l₂ ⟧t ⟦ r₂ ⟧t i
  ⟦ I.π-⇒+ t l r i ⟧t = π-⇒+ ⟦ t ⟧t ⟦ l ⟧t ⟦ r ⟧t i


