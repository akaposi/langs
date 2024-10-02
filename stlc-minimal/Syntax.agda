{-# OPTIONS --cubical #-}
-- {-# OPTIONS --allow-unsolved-metas #-} 

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path

module stlc-minimal.Syntax where


data Ty : Type 

data Ty where
    ι   : Ty
    _⇒_ : Ty → Ty → Ty

caseTy : ∀ {ℓ} → {A : Type ℓ} → (a0 aS : A) → Ty → A
caseTy a0 aS ι = a0
caseTy a0 aS (ty ⇒ ty₁) = aS

ιnot⇒ : ∀ {u}{v} → ¬ (ι ≡ u ⇒ v)
ιnot⇒ eq = subst (caseTy Ty ⊥) eq ι

⇒notι : ∀ {u}{v} → ¬ (u ⇒ v ≡ ι)
⇒notι eq = subst (caseTy ⊥ Ty) eq ι

inj⇒₁ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → u ≡ u'
inj⇒₁ e = cong (λ { (u ⇒ v) → u ; _ → ι } ) e
inj⇒₂ : ∀{u v u' v' : Ty} → u ⇒ v ≡ u' ⇒ v' → v ≡ v'
inj⇒₂ e = cong (λ { (u ⇒ v) → v ; _ → ι } ) e

discreteTy : (u v : Ty) → Dec (u ≡ v)
discreteTy ι ι = yes refl
discreteTy ι (v ⇒ v₁) = no (λ p → ιnot⇒ p)
discreteTy (u ⇒ u₁) ι = no λ p → ⇒notι p
discreteTy (u ⇒ u₁) (v ⇒ v₁) with discreteTy u v | discreteTy u₁ v₁
... | yes p | yes p₁ = yes λ i → p i ⇒ (p₁ i)
... | yes p | no ¬p = no λ where x → ¬p (inj⇒₂ x)
... | no ¬p | yes p = no λ where x → ¬p (inj⇒₁ x)
... | no ¬p | no ¬p₁ = no λ where x → ¬p (inj⇒₁ x)

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
inj▸₂ e = cong (λ { (Γ₁ ▸ A₁) → A₁; _ → ι } ) e 

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
  A B : Ty
  
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

_[_]′ = _[_]
q′ = q
γ ↑ = γ ∘ p , q
⟨_⟩ = id ,_


_[_]* : Tm Γ A → Sub Δ Γ → Tm Δ A
_[_]= : (a : Tm Γ A)(γ : Sub Δ Γ) → a [ γ ]* ≡ a [ γ ]

TmSet a a' e e' i j [ γ ]* = TmSet (a [ γ ]*) (a' [ γ ]*) (cong _[ γ ]* e) (cong _[ γ ]* e') i j
(a [ γ ]) [ δ ]* = a [ γ ∘ δ ]*
[]-∘ a γ δ i [ θ ]* = a [ assoc γ δ θ (~ i) ]*
[]-id a i [ γ ]* = a [ idl γ i ]*
q [ γ ]* = q [ γ ]
▸-β₂ γ a i [ δ ]* = (cong (q [_]) (,-∘ γ a δ) ∙ ▸-β₂ (γ ∘ δ) (a [ δ ]) ∙ sym (a [ δ ]=)) i
app t a [ γ ]* = app (t [ γ ]*) (a [ γ ]*)
app-[] t a γ i [ δ ]* = app (t [ γ ∘ δ ]*) (a [ γ ∘ δ ]*)
lam t [ γ ]* = lam t [ γ ] 
lam-[] t γ i [ δ ]* = (([]-∘ (lam t) γ δ) ∙ cong (_[ δ ]) (lam-[] t γ)) i
⇒-β t a i [ γ ]* = ((t [ ⟨ a ⟩ ∘ γ ]=) ∙ ([]-∘ t (⟨ a ⟩) γ) ∙ (cong (_[ γ ]) (sym (⇒-β t a))) ∙ (app-[] (lam t) a γ ) ∙ (cong (λ x → app (lam t [ γ ]) x) (sym (a [ γ ]=)))) (~ i)
⇒-η t i [ γ ]* = ((cong (_[ γ ]) (⇒-η t)) ∙ (sym (t [ γ ]=))  ) i



(TmSet a a' e e' i j [ γ ]=) = isProp→SquareP (λ i₁ j₁ → TmSet (TmSet (a [ γ ]*) (a' [ γ ]*) (cong _[ γ ]* e) (cong _[ γ ]* e') i₁ j₁)  ((TmSet a a' e e' i₁ j₁) [ γ ])) (λ i₁ → a [ γ ]=) (λ i₁ → a' [ γ ]=) (λ j₁ → e j₁ [ γ ]=) (λ j₁ → e' j₁ [ γ ]=) i j 
((a [ γ ]) [ δ ]=) = (a [ γ ∘ δ ]=) ∙ ([]-∘ a γ δ) 
([]-∘ a γ δ i [ θ ]=) j = isSet→isSet' TmSet
  (((a [ γ ∘ δ ∘ θ ]=) ∙ []-∘ a (γ ∘ δ) θ))
  ((((a [ γ ∘ (δ ∘ θ) ]=) ∙ []-∘ a γ (δ ∘ θ)) ∙ []-∘ (a [ γ ]) δ θ))
  (λ i → a [ assoc γ δ θ (~ i) ]*)
  (λ i → []-∘ a γ δ i [ θ ])
  i j
([]-id a i [ γ ]=) j = isSet→isSet' TmSet (λ j → ((a [ id ∘ γ ]=) ∙ []-∘ a id γ) j) (λ j → (a [ γ ]=) j) (λ i → a [ idl γ i ]*) (λ i → []-id a i [ γ ]) i j
(q [ γ ]=) = refl
(▸-β₂ γ₁ a i₁ [ γ ]=) i = {!   !}
(app t a [ γ ]=) i = ((cong (λ x → app (t [ γ ]*) x) (a [ γ ]=)) ∙ (cong (λ x → app x (a [ γ ])) (t [ γ ]=)) ∙ (sym (app-[] t a γ))) i
(app-[] a a₁ γ₁ i₁ [ γ ]=) i = {!   !}
(lam-[] a γ₁ i₁ [ γ ]=) i = {!   !}
(⇒-β a a₁ i₁ [ γ ]=) i = {!   !}
(⇒-η a i₁ [ γ ]=) i = {!   !}
(lam a [ γ ]=) = refl 
-- (a ≡ b) =  (f : 𝕀 → A)        f i0 = a,  f i1 = b


