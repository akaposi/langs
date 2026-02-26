{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ) hiding (assoc; id)

module stlc-sum.Syntax where


data Ty : Type 

data Ty where
    ⊥ₗ Unitₗ  : Ty
    _⇒_  _+ₗ_ : Ty → Ty → Ty

caseTy : ∀ {ℓ} → {A : Type ℓ} → (a0 aS aSS : A) → Ty → A
-- caseTy a0 aS aSS ⊥ₗ = a0
-- caseTy a0 aS aSS (Ty₁ ⇒ Ty₂) = aS
-- caseTy a0 aS aSS (Ty₁ +ₗ Ty₂) = aSS
caseTy = {!   !}

-- ⊥ₗnot+ :  ∀ {u}{v} → ¬ (⊥ₗ ≡ u +ₗ v)
-- ⊥ₗnot+ eq = subst (caseTy Ty Ty ⊥) eq ⊥ₗ

-- ⊥ₗnot⇒ :  ∀ {u}{v} → ¬ (⊥ₗ ≡ u ⇒ v)
-- ⊥ₗnot⇒ eq = subst (caseTy Ty ⊥ Ty) eq ⊥ₗ
  
-- +not⇒ : ∀ {u v u' v'} → ¬ (u +ₗ v ≡ u' ⇒ v')
-- +not⇒ eq = subst (caseTy ⊥ ⊥ Ty) eq ⊥ₗ

inj⇒₁ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → u ≡ u'
inj⇒₁ e = cong (λ { (u ⇒ v) → u ; _ → ⊥ₗ } ) e 
inj⇒₂ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → v ≡ v'
inj⇒₂ e = cong (λ { (u ⇒ v) → v ; _ → ⊥ₗ } ) e

inj+ₗ₁ : ∀{u v u' v' : Ty} → u +ₗ v ≡ u' +ₗ v' → u ≡ u'
inj+ₗ₁ e = cong (λ { (u +ₗ v) → u ; _ → ⊥ₗ } ) e 
inj+ₗ₂ : ∀{u v u' v' : Ty} → u +ₗ v ≡ u' +ₗ v' → v ≡ v'
inj+ₗ₂ e =  cong (λ { (u +ₗ v) → v ; _ → ⊥ₗ } ) e 

discreteTy : (u v : Ty) → Dec (u ≡ v)
discreteTy = {!   !}
-- discreteTy ⊥ₗ ⊥ₗ = yes refl
-- discreteTy ⊥ₗ (v ⇒ v₁) = no λ p → ⊥ₗnot⇒ p
-- discreteTy ⊥ₗ (v +ₗ v₁) = no λ p → ⊥ₗnot+ p
-- discreteTy (u ⇒ u₁) ⊥ₗ = no λ p → ⊥ₗnot⇒ (sym p)
-- discreteTy (u ⇒ u₁) (v ⇒ v₁) with discreteTy u v | discreteTy u₁ v₁
-- ... | yes p | yes p₁ = yes λ i → p i ⇒ (p₁ i)
-- ... | yes p | no ¬p = no λ where x → ¬p (inj⇒₂ x)
-- ... | no ¬p | yes p = no λ where x → ¬p (inj⇒₁ x)
-- ... | no ¬p | no ¬p₁ = no λ where x → ¬p (inj⇒₁ x) 
-- discreteTy (u ⇒ u₁) (v +ₗ v₁) = no (λ p → +not⇒ (sym p))
-- discreteTy (u +ₗ u₁) ⊥ₗ = no λ p → ⊥ₗnot+ (sym p)
-- discreteTy (u +ₗ u₁) (v ⇒ v₁) = no (λ p → +not⇒ p)
-- discreteTy (u +ₗ u₁) (v +ₗ v₁) with discreteTy u v | discreteTy u₁ v₁
-- ... | yes p | yes p₁ = yes λ i → p i +ₗ (p₁ i) 
-- ... | yes p | no ¬p = no λ where x → ¬p (inj+ₗ₂ x)
-- ... | no ¬p | yes p =  no λ where x → ¬p (inj+ₗ₁ x)
-- ... | no ¬p | no ¬p₁ =  no λ where x → ¬p (inj+ₗ₁ x)

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

  ttₗ : Tm Γ Unitₗ
  ttₗ-[] : ∀ (γ : Sub Δ Γ) → ttₗ [ γ ] ≡ ttₗ 
  
  unit-η : ∀ (t : Tm Γ Unitₗ) → t ≡ ttₗ

  inlₗ  : Tm Γ A → Tm Γ (A +ₗ B) 
  inlₗ-[] :  ∀ (a : Tm Γ A)(γ : Sub Δ Γ) → inlₗ {B = B} a [ γ ] ≡ inlₗ {B = B} (a [ γ ]) 
  inrₗ  : Tm Γ B → Tm Γ (A +ₗ B)  
  inrₗ-[] : ∀ (b : Tm Γ B)(γ : Sub Δ Γ) → inrₗ {A = A} b [ γ ] ≡ inrₗ {A = A} (b [ γ ]) 

  case+ : Tm Γ (A +ₗ B) → Tm (Γ ▸ A) C → Tm (Γ ▸ B) C → Tm Γ C 
  case+[] :  ∀ (t : Tm Γ (A +ₗ B)) (a :  Tm (Γ ▸ A) C)(b :  Tm (Γ ▸ B) C) (γ : Sub Δ Γ) → case+ t a b [ γ ] ≡ case+ (t [ γ ]) (a [ γ ↑ ]) (b [ γ ↑ ])

  +-β₁ : ∀ (t : Tm Γ A) (a : Tm (Γ ▸ A) C)(b : Tm (Γ ▸ B) C) → case+ (inlₗ {B = B} t) a b ≡ a [ id , t ]
  +-β₂ : ∀ (t : Tm Γ B) (a : Tm (Γ ▸ A) C)(b : Tm (Γ ▸ B) C) → case+ (inrₗ {A = A} t) a b ≡ b [ id , t ]

 
  
-- weak eta case t inl inr =  t 
  -- +-η : ∀ (t : Tm Γ (A +ₗ B)) → case+ t (inlₗ q) (inrₗ q) ≡ t 
  -- +-η : ∀ (t : Tm Γ (A +ₗ B))(a : Tm (Γ ▸ A) A)(b : Tm (Γ ▸ B) B) → case+ t (inlₗ a) (inrₗ b) ≡ t 
-- adding empty, exfalso : Tm Unit empty -> Tm Unit A
-- unit, tt
-- Bool := unit + unit
-- lam q =/ lam (if q then t else f)

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



 
     