{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ) hiding (assoc; id)
module stlc-sum.Weakening where
open import stlc-sum.Syntax as S 

private variable
  n : ℕ
  Γ Δ Θ Ξ : Con
  A A₁ A₂ B : S.Ty

infixl 4 _↑' _∘p

data Wk : S.Con → S.Con → Type where
  ε : Wk S.◆ S.◆
  _∘p : Wk Δ Γ → Wk (Δ S.▸ A) Γ
  _↑' : Wk Δ Γ → Wk (Δ S.▸ A) (Γ S.▸ A)

discreteWk : (w₁ w₂ : Wk Δ Γ) → Dec (w₁ ≡ w₂) 
discreteWk ε ε = yes refl
discreteWk (w₁ ∘p) (w₂ ∘p) with discreteWk w₁ w₂
... | yes p₁ = yes (λ i → (p₁ i ∘p))
... | no ¬p = no (λ eq → ¬p {! fun  !})
discreteWk (w₁ ∘p) (w₂ ↑') = {!   !}
discreteWk (w₁ ↑') w₂ = {!   !}

isWkSet : isSet (Wk Δ Γ)
isWkSet = Discrete→isSet discreteWk 

Wk-emb : Wk Δ Γ → S.Sub Δ Γ
Wk-emb ε = S.ε
Wk-emb (γ ∘p) = Wk-emb γ S.∘ S.p
Wk-emb (γ ↑') = Wk-emb γ S.↑

infixl 40 _∘'_ 
_∘'_  : Wk Δ Γ → Wk Θ Δ → Wk Θ Γ 
γ ∘' ε = γ
γ ∘' (δ ∘p) = γ ∘' δ ∘p
(γ ∘p) ∘' (δ ↑') = γ ∘' δ ∘p
(γ ↑') ∘' (δ ↑') = γ ∘' δ ↑'

Wk-emb-∘ : (γ : Wk Δ Γ) (δ : Wk Θ Δ) → Wk-emb (γ ∘' δ) ≡ Wk-emb γ S.∘ Wk-emb δ
Wk-emb-∘ γ ε = sym (S.idr (Wk-emb γ)) ∙ λ i → Wk-emb γ ∘ S.◆-η  (~ i) 
Wk-emb-∘ γ (δ ∘p) = (λ i → Wk-emb-∘ γ δ i ∘ p) ∙ sym (S.assoc (Wk-emb γ) (Wk-emb δ) p) 
Wk-emb-∘ (γ ∘p) (δ ↑') = ((λ i → Wk-emb-∘ γ δ i ∘ p) ∙ sym (S.assoc (Wk-emb γ) (Wk-emb δ) p)) ∙ (λ i → Wk-emb γ ∘  ▸-β₁ (Wk-emb δ ∘ p) q (~ i)) ∙ (S.assoc (Wk-emb γ) p (Wk-emb δ ↑))
Wk-emb-∘ (γ ↑') (δ ↑') = (λ i → (Wk-emb-∘ γ δ) i ↑) ∙ S.↑-∘ (Wk-emb γ) (Wk-emb δ)

assoc' : (γ : Wk Δ Γ) (δ : Wk Θ Δ) (θ : Wk Ξ Θ) → γ ∘' (δ ∘' θ) ≡ γ ∘' δ ∘' θ
assoc' γ δ ε = refl
assoc' γ δ (θ ∘p) = λ i → assoc' γ δ θ i ∘p
assoc' γ (δ ∘p) (θ ↑') = λ i → assoc' γ δ θ i ∘p
assoc' (γ ∘p) (δ ↑') (θ ↑') = λ i → assoc' γ δ θ i ∘p
assoc' (γ ↑') (δ ↑') (θ ↑') = λ i → assoc' γ δ θ i ↑'

id' : Wk Γ Γ
id' {Γ ▸ A} = id' ↑'
id' {◆} = ε

Wk-emb-id : Wk-emb id' ≡ S.id {Γ}
Wk-emb-id {Γ ▸ A} = (λ i → ( Wk-emb-id i ↑)) ∙ S.↑-id
Wk-emb-id {◆} = S.◆-η

idr' : (γ : Wk Δ Γ) → γ ∘' id' ≡ γ
idr' ε = refl
idr' (γ ∘p) = λ i → (idr' γ i ∘p)
idr' (γ ↑') = λ i → (idr' γ i ↑')

idl' : (γ : Wk Δ Γ) → id' ∘' γ ≡ γ
idl' ε = refl
idl' (γ ∘p) = λ i → (idl' γ i ∘p)
idl' (γ ↑') = λ i → (idl' γ i ↑')

infixl 4 _[p]
data Var : S.Con → S.Ty → Type where
  q : Var (Γ S.▸ A) A
  _[p] : Var Γ A → Var (Γ S.▸ B) A

discreteVar : ∀ {Γ A} → (v₁ v₂ : Var Γ A) → Dec (v₁ ≡ v₂) 
discreteVar = {!   !}

isVarSet : isSet (Var Γ A)
isVarSet = Discrete→isSet discreteVar

Var-emb : Var Γ A → S.Tm Γ A
Var-emb q = S.q
Var-emb (a [p]) = Var-emb a S.[ S.p ]

infixl 40 _[_]'
_[_]' : Var Γ A → Wk Δ Γ → Var Δ A
a [ ε ]' = a
a [ γ ∘p ]' = a [ γ ]' [p]
q [ γ ↑' ]' = q
(a [p]) [ γ ↑' ]' = a [ γ ]' [p] 

Var-emb-[] : (a : Var Γ A) (γ : Wk Δ Γ) → Var-emb (a [ γ ]') ≡ Var-emb a S.[ Wk-emb γ ]
Var-emb-[] a (γ ∘p) = (λ i →  Var-emb-[] a γ i [ p ]) ∙ sym (S.[]-∘ (Var-emb a) (Wk-emb γ) p)
Var-emb-[] q (γ ↑') = sym (S.▸-β₂ _ _)
Var-emb-[] (a [p]) (γ ↑') = (λ i → Var-emb-[] a γ i [ p ]) ∙ sym (S.[]-∘ (Var-emb a) (Wk-emb γ) p) ∙ (λ i → Var-emb a [ S.▸-β₁ (Wk-emb γ ∘ p) q (~ i) ]) ∙ S.[]-∘ (Var-emb a) p (Wk-emb γ ↑)

[]-∘' : (a : Var Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘' δ ]' ≡ a [ γ ]' [ δ ]'
[]-∘' a γ ε = refl 
[]-∘' a γ (δ ∘p) = λ i → []-∘' a γ δ i [p]
[]-∘' a (γ ∘p) (δ ↑') = λ i → []-∘' a γ δ i [p]
[]-∘' q (γ ↑') (δ ↑') = refl
[]-∘' (a [p]) (γ ↑') (δ ↑') = λ i → []-∘' a γ δ i [p]

[]-id' : (a : Var Γ A) → a [ id' ]' ≡ a --a [ id ] ≡ a
[]-id' q = refl
[]-id' (a [p]) = λ i → []-id' a i [p]