{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ) hiding (assoc; id)

module stlc-sum-cover.Syntax where


data Ty : Type 

data Ty where
    ⊥ₗ : Ty
    _⇒_ : Ty → Ty → Ty
    _+_ : Ty → Ty → Ty

caseTy : ∀ {ℓ} → {A : Type ℓ} → (a⊥ a⇒ a+ : A) → Ty → A
caseTy a⊥ a⇒ a+ ⊥ₗ = a⊥
caseTy a⊥ a⇒ a+ (_ ⇒ _) = a⇒
caseTy a⊥ a⇒ a+ (_ + _) = a+

inj⇒₁ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → u ≡ u'
inj⇒₁ e = cong (λ { (u ⇒ v) → u ; _ → ⊥ₗ } ) e 
inj⇒₂ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → v ≡ v'
inj⇒₂ e = cong (λ { (u ⇒ v) → v ; _ → ⊥ₗ } ) e

inj+₁ : ∀{u v u' v' : Ty} → u + v ≡ u' + v' → u ≡ u'
inj+₁ e = cong (λ { (u + v) → u ; _ → ⊥ₗ } ) e 
inj+₂ : ∀{u v u' v' : Ty} → u + v ≡ u' + v' → v ≡ v'
inj+₂ e = cong (λ { (u + v) → v ; _ → ⊥ₗ } ) e

discreteTy : (u v : Ty) → Dec (u ≡ v)
discreteTy ⊥ₗ ⊥ₗ = yes refl
discreteTy ⊥ₗ (_ ⇒ _) = no (λ e → subst (caseTy Ty ⊥ ⊥) e ⊥ₗ)
discreteTy ⊥ₗ (_ + _) = no (λ e → subst (caseTy Ty ⊥ ⊥) e ⊥ₗ)
discreteTy (_ ⇒ _) ⊥ₗ = no (λ e → subst (caseTy ⊥ Ty ⊥) e ⊥ₗ)
discreteTy (_ ⇒ _) (_ + _) = no (λ e → subst (caseTy ⊥ Ty ⊥) e ⊥ₗ)
discreteTy (_ + _) ⊥ₗ = no (λ e → subst (caseTy ⊥ ⊥ Ty) e ⊥ₗ)
discreteTy (_ + _) (_ ⇒ _) = no (λ e → subst (caseTy ⊥ ⊥ Ty) e ⊥ₗ)
discreteTy (u₁ ⇒ v₁) (u₂ ⇒ v₂) with discreteTy u₁ u₂ | discreteTy v₁ v₂
... | yes p | yes q = yes (λ i → p i ⇒ q i)
... | yes _ | no ¬q = no (λ e → ¬q (inj⇒₂ e))
... | no ¬p | _     = no (λ e → ¬p (inj⇒₁ e))
discreteTy (u₁ + v₁) (u₂ + v₂) with discreteTy u₁ u₂ | discreteTy v₁ v₂
... | yes p | yes q = yes (λ i → p i + q i)
... | yes _ | no ¬q = no (λ e → ¬q (inj+₂ e))
... | no ¬p | _     = no (λ e → ¬p (inj+₁ e))

isTySet : isSet Ty 
isTySet = Discrete→isSet discreteTy

infixl 4 _▸_
data Con : Type where
  _▸_ : Con → Ty → Con
  ◆ : Con

caseCon : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → Con → A
caseCon a0 aS (x ▸ x₁) = a0
caseCon a0 aS ◆ = aS 

◆not▸ : ∀ {Γ₁}{Γ₂} → ¬ (◆ ≡ (Γ₁ ▸ Γ₂))
◆not▸ eq = subst (caseCon ⊥ Con) eq ◆ 

▸not◆ : ∀ {Γ₁}{Γ₂} → ¬ ((Γ₁ ▸ Γ₂) ≡ ◆)
▸not◆ eq = subst (caseCon Con ⊥) eq ◆ 

inj▸₁ : ∀{Γ₁ Γ₂ : Con}{A₁ A₂ : Ty} → (Γ₁ ▸ A₁) ≡ (Γ₂ ▸ A₂) → Γ₁ ≡ Γ₂
inj▸₁ e = cong (λ { (Γ₁ ▸ A₁) → Γ₁; _ → ◆ } ) e 
inj▸₂ : ∀{Γ₁ Γ₂ : Con}{A₁ A₂ : Ty} → (Γ₁ ▸ A₁) ≡ (Γ₂ ▸ A₂) → A₁ ≡ A₂
inj▸₂ e = cong (λ { (Γ₁ ▸ A₁) → A₁; _ → ⊥ₗ } ) e 

discreteCon : (u v : Con) → Dec (u ≡ v)
discreteCon (Γ₁ ▸ A₁) (Γ₂ ▸ A₂) with discreteCon Γ₁ Γ₂ | discreteTy A₁ A₂
... | yes Γ₁≡Γ₂ | yes A₁≡A₂ = yes (λ i → (Γ₁≡Γ₂ i) ▸ (A₁≡A₂ i))
... | yes _ | no ¬A₁≡A₂ = no (λ e → ¬A₁≡A₂ (inj▸₂ e))
... | no ¬Γ₁≡Γ₂ | _ = no λ e → ¬Γ₁≡Γ₂ (inj▸₁ e)
discreteCon (Γ₁ ▸ A₁) ◆ = no ▸not◆
discreteCon ◆ (Γ₂ ▸ A₂) = no ◆not▸
discreteCon ◆ ◆ = yes refl  

isConSet : isSet Con
isConSet = Discrete→isSet discreteCon

private variable
  Γ Δ Θ Ξ : Con
  A B C D : Ty
  
data Sub : Con → Con → Type  -- parallel Substitution
data Tm : Con → Ty → Type

private
  infixl 40 _[_]′
  _[_]′ : Tm Γ A → Sub Δ Γ → Tm Δ A
  q′ : Tm (Γ ▸ A) A

infixl 4 _↑
_↑ : Sub Δ Γ → Sub (Δ ▸ A) (Γ ▸ A)
⟨_⟩ : Tm Γ A → Sub Γ (Γ ▸ A)

infixl 40 _∘_
infixl 4 _,_

data Sub where
  SubSet : isSet (Sub Δ Γ)
  _∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  assoc : (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) → γ ∘ (δ ∘ θ) ≡ γ ∘ δ ∘ θ

  id : Sub Γ Γ
  idr : (γ : Sub Δ Γ) → γ ∘ id ≡ γ
  idl : (γ : Sub Δ Γ) → id ∘ γ ≡ γ
  p : Sub (Γ ▸ A) Γ
  _,_ : Sub Δ Γ → Tm Δ A → Sub Δ (Γ ▸ A)
  ,-∘ :
    (γ : Sub Δ Γ) (a : Tm Δ A) (δ : Sub Θ Δ) → (γ , a) ∘ δ ≡ (γ ∘ δ , a [ δ ]′)

  ▸-β₁ : (γ : Sub Δ Γ) (a : Tm Δ A) → p ∘ (γ , a) ≡ γ
  ▸-η : (p , q′) ≡ id {Γ ▸ A}

  ε : Sub Γ ◆
  ε-∘ : (γ : Sub Δ Γ) → ε ∘ γ ≡ ε
  ◆-η : ε ≡ id

data Tm where
  TmSet : isSet (Tm Γ A)
  _[_] : Tm Γ A → Sub Δ Γ → Tm Δ A
  []-∘ : (a : Tm Γ A) (γ : Sub Δ Γ) (δ : Sub Θ Δ) → a [ γ ∘ δ ] ≡ a [ γ ] [ δ ]
  []-id : (a : Tm Γ A) → a [ id ] ≡ a
 
  q : Tm (Γ ▸ A) A
  ▸-β₂ : (γ : Sub Δ Γ) (a : Tm Δ A) → q [ γ , a ] ≡ a

  app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  app-[] :
    ∀ (f : Tm Γ (A ⇒ B)) a (γ : Sub Δ Γ) →
    app f a [ γ ] ≡ app (f [ γ ]) (a [ γ ])

  lam : Tm (Γ ▸ A) B → Tm Γ (A ⇒ B)
  lam-[] : (b : Tm (Γ ▸ A) B) (γ : Sub Δ Γ) → lam b [ γ ] ≡ lam (b [ γ ↑ ])

  ⇒-β : ∀ (b : Tm (Γ ▸ A) B) a → app (lam b) a ≡ b [ ⟨ a ⟩ ]
  ⇒-η : (f : Tm Γ (A ⇒ B)) → lam (app (f [ p ]) q) ≡ f

  exfalsoₗ : Tm Γ ⊥ₗ → Tm Γ A
  exfalsoₗ-[] : ∀ t (γ : Sub Δ Γ) → exfalsoₗ {A = A} t [ γ ] ≡ exfalsoₗ (t [ γ ])

  ⊥ₗ-η : ∀ {Γ} (t : Tm Γ ⊥ₗ) → t ≡ exfalsoₗ {A = ⊥ₗ} t

  π-⇒0 : ∀ {Γ A B} (t : Tm Γ ⊥ₗ) (u : Tm Γ A) 
       → app (exfalsoₗ {A = A ⇒ B} t) u ≡ exfalsoₗ {A = B} t

  -- Sum type
  inl : Tm Γ A → Tm Γ (A + B)
  inr : Tm Γ B → Tm Γ (A + B)
  caseₗ : Tm Γ (A + B) → Tm (Γ ▸ A) C → Tm (Γ ▸ B) C → Tm Γ C

  inl-[] : ∀ (a : Tm Γ A) (γ : Sub Δ Γ) → inl {B = B} a [ γ ] ≡ inl (a [ γ ])
  inr-[] : ∀ (b : Tm Γ B) (γ : Sub Δ Γ) → inr {A = A} b [ γ ] ≡ inr (b [ γ ])
  caseₗ-[] : ∀ (s : Tm Γ (A + B)) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C) (γ : Sub Δ Γ)
           → caseₗ s l r [ γ ] ≡ caseₗ (s [ γ ]) (l [ γ ↑ ]) (r [ γ ↑ ])

  +-β₁ : ∀ (a : Tm Γ A) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C)
       → caseₗ (inl a) l r ≡ l [ ⟨ a ⟩ ]
  +-β₂ : ∀ (b : Tm Γ B) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C) 
       → caseₗ (inr b) l r ≡ r [ ⟨ b ⟩ ]

  +-η : ∀ (s : Tm Γ (A + B)) → caseₗ s (inl q) (inr q) ≡ s

  -- Commuting conversions for sum
  π-+⇒ : ∀ {Γ A B C D} (s : Tm Γ (A + B)) (l : Tm (Γ ▸ A) (C ⇒ D)) (r : Tm (Γ ▸ B) (C ⇒ D)) (u : Tm Γ C)
       → app (caseₗ s l r) u ≡ caseₗ s (app l (u [ p ])) (app r (u [ p ]))
  π-+0 : ∀ {Γ A B C} (s : Tm Γ (A + B)) (l : Tm (Γ ▸ A) ⊥ₗ) (r : Tm (Γ ▸ B) ⊥ₗ)
       → exfalsoₗ {A = C} (caseₗ s l r) ≡ caseₗ s (exfalsoₗ l) (exfalsoₗ r)
  π-++ : ∀ {Γ A B C D E} (s : Tm Γ (A + B)) (l₁ : Tm (Γ ▸ A) (C + D)) (r₁ : Tm (Γ ▸ B) (C + D))
           (l₂ : Tm (Γ ▸ C) E) (r₂ : Tm (Γ ▸ D) E)
       → caseₗ (caseₗ s l₁ r₁) l₂ r₂ ≡ caseₗ s (caseₗ l₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) (caseₗ r₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ]))
  π-⇒+ : ∀ {Γ A B C} (t : Tm Γ ⊥ₗ) (l : Tm (Γ ▸ A) C) (r : Tm (Γ ▸ B) C) 
       → caseₗ (exfalsoₗ {A = A + B} t) l r ≡ exfalsoₗ {A = C} t

_[_]′ = _[_]
q′ = q
γ ↑ = γ ∘ p , q
⟨_⟩ = id ,_

↑-∘ :
  (γ : Sub Δ Γ) (δ : Sub Θ Δ) →
  Path (Sub (Θ ▸ A) (Γ ▸ A)) (γ ∘ δ ↑) ((γ ↑) ∘ (δ ↑))
↑-∘ γ δ = eqToPath (ap (λ z → z , q) (Indsym (pathToEq (assoc γ δ p))) Ind∙ 
            ((ap (λ z → (γ ∘ z , q)) (Indsym (pathToEq (▸-β₁ _ _))) Ind∙ 
            ap (λ z → (z , q)) (pathToEq (assoc γ p (δ ↑)))) Ind∙ 
            ap (λ z → (γ ∘ p ∘ (δ ↑) , z) ) (Indsym (pathToEq (▸-β₂ (δ ∘ p) q))))  Ind∙ 
            (Indsym(pathToEq (,-∘ (γ ∘ p) q (δ ↑)))))  

↑-id : (id ↑) ≡ id {Γ ▸ A}
↑-id =  congS (λ z → (z , q)) (idl p) ∙ ▸-η

↑-⟨⟩ : (γ : Sub Δ Γ) (a : Tm Δ A) → (γ ↑) ∘ ⟨ a ⟩ ≡ (γ , a)
↑-⟨⟩ γ a = (,-∘ _ _ _) ∙ congS (λ z → (z , q [ ⟨ a ⟩ ]′)) (sym (assoc γ p ⟨ a ⟩)) ∙ 
          (congS (λ z → (γ ∘ z , q [ ⟨ a ⟩ ]′)) (▸-β₁ _ _) ∙ 
            congS (λ z →  (z , q [ ⟨ a ⟩ ]′))  (idr _)) ∙ 
          congS (λ z → γ , z) (▸-β₂ _ _)



 
     