{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ) hiding (assoc; id)
module stlc-sum.NormalForm where
open import stlc-sum.Syntax as S 
open import stlc-sum.Weakening

private variable
  n : ℕ
  Γ Δ Θ : S.Con
  A B P : S.Ty

data Ne : S.Con → S.Ty → Type
data Nf : S.Con → S.Ty → Type

data Ne where
  var : Var Γ A → Ne Γ A
  app : Ne Γ (A S.⇒ B) → Nf Γ A → Ne Γ B
  case : Ne Γ (A +ₗ B) → Nf (Γ S.▸ A) P → Nf (Γ S.▸ B) P → Ne Γ P
  exfalsoₗ : Ne Γ S.⊥ₗ → Ne Γ A

data Nf where
  lam : Nf (Γ S.▸ A) B → Nf Γ (A S.⇒ B)
  +-ne : Ne Γ (A S.+ₗ B) → Nf Γ (A S.+ₗ B) 
  ⊥ₗ-ne : Ne Γ S.⊥ₗ → Nf Γ S.⊥ₗ
  inlₗ : ∀ {B = B} → Nf Γ A → Nf Γ (A S.+ₗ B)
  inrₗ : ∀ {A = A} → Nf Γ B → Nf Γ (A S.+ₗ B)
  ttₗ : Nf Γ S.Unitₗ

discreteNe : ∀ {Γ A} → (n₁ n₂ : Ne Γ A) → Dec (n₁ ≡ n₂) 
discreteNe = {!   !}

isNeSet : isSet (Ne Γ A)
isNeSet = Discrete→isSet discreteNe

discreteNf : ∀ {Γ A} → (n₁ n₂ : Nf Γ A) → Dec (n₁ ≡ n₂) 
discreteNf = {!   !}

isNfSet : isSet (Nf Γ A)
isNfSet = Discrete→isSet discreteNf

Ne-emb : Ne Γ A → S.Tm Γ A
Nf-emb : Nf Γ A → S.Tm Γ A

Ne-emb (var a) = Var-emb a
Ne-emb (app f a) = S.app (Ne-emb f) (Nf-emb a)
Ne-emb (case a₁ a₂ t) = S.case+ (Ne-emb a₁) (Nf-emb a₂) (Nf-emb t)
Ne-emb (exfalsoₗ a) = exfalsoₗ (Ne-emb a)

Nf-emb (lam a) = S.lam (Nf-emb a)
Nf-emb (+-ne t) = Ne-emb t
Nf-emb (⊥ₗ-ne t) = Ne-emb t
Nf-emb (inlₗ a) = S.inlₗ (Nf-emb a)
Nf-emb (inrₗ a) = S.inrₗ (Nf-emb a)
Nf-emb ttₗ = S.ttₗ


infixl 40 _[_]ᴺᵉ _[_]ᴺᶠ
_[_]ᴺᵉ : Ne Γ A → Wk Δ Γ → Ne Δ A
_[_]ᴺᶠ : Nf Γ A → Wk Δ Γ → Nf Δ A

var a [ γ ]ᴺᵉ = var (a [ γ ]')
app f a [ γ ]ᴺᵉ = app (f [ γ ]ᴺᵉ) (a [ γ ]ᴺᶠ)
case t a b [ γ ]ᴺᵉ = case (t [ γ ]ᴺᵉ) (a [ γ ↑' ]ᴺᶠ) (b [ γ ↑' ]ᴺᶠ)
exfalsoₗ a [ γ ]ᴺᵉ = exfalsoₗ (a [ γ ]ᴺᵉ)

lam b [ γ ]ᴺᶠ = lam (b [ γ ↑' ]ᴺᶠ)
+-ne t [ γ ]ᴺᶠ = +-ne (t [ γ ]ᴺᵉ)
⊥ₗ-ne t [ γ ]ᴺᶠ = ⊥ₗ-ne (t [ γ ]ᴺᵉ)
inlₗ a [ γ ]ᴺᶠ = inlₗ (a [ γ ]ᴺᶠ)
inrₗ a [ γ ]ᴺᶠ = inrₗ (a [ γ ]ᴺᶠ)
ttₗ [ γ ]ᴺᶠ = ttₗ

Ne-emb-[] :
  (a : Ne Γ A) (γ : Wk Δ Γ) → Ne-emb (a [ γ ]ᴺᵉ) ≡ Ne-emb a S.[ Wk-emb γ ]
Nf-emb-[] :
  (a : Nf Γ A) (γ : Wk Δ Γ) → Nf-emb (a [ γ ]ᴺᶠ) ≡ Nf-emb a S.[ Wk-emb γ ]

Ne-emb-[] (var x) γ = Var-emb-[] _ _
Ne-emb-[] (app f a) γ = (λ i → app (Ne-emb-[] f γ i) (Nf-emb-[] a γ i)) ∙ sym (S.app-[] (Ne-emb f) (Nf-emb a) (Wk-emb γ))
Ne-emb-[] (case t a b) γ = (λ i → case+ (Ne-emb-[] t γ i) (Nf-emb-[] a (γ ↑') i) (Nf-emb-[] b (γ ↑') i)) ∙ sym (S.case+[] (Ne-emb t) (Nf-emb a) (Nf-emb b) (Wk-emb γ))
Ne-emb-[] (exfalsoₗ x) γ = (λ i → exfalsoₗ (Ne-emb-[] x γ i)) ∙ sym (S.exfalsoₗ-[] (Ne-emb x) (Wk-emb γ))

Nf-emb-[] (lam a) γ = (λ i → lam (Nf-emb-[] a (γ ↑') i)) ∙ sym (S.lam-[] (Nf-emb a) (Wk-emb γ))
Nf-emb-[] (+-ne a) γ = Ne-emb-[] a γ
Nf-emb-[] (⊥ₗ-ne a) γ = Ne-emb-[] a γ
Nf-emb-[] (inlₗ a) γ = (λ i → inlₗ (Nf-emb-[] a γ i)) ∙ sym (S.inlₗ-[] (Nf-emb a) (Wk-emb γ))
Nf-emb-[] (inrₗ a) γ = (λ i → inrₗ (Nf-emb-[] a γ i)) ∙ sym (S.inrₗ-[] (Nf-emb a) (Wk-emb γ))
Nf-emb-[] (ttₗ)  γ = sym (S.ttₗ-[] (Wk-emb γ)) 

[]ᴺᵉ-∘ :
  (a : Ne Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘' δ ]ᴺᵉ ≡ a [ γ ]ᴺᵉ [ δ ]ᴺᵉ
[]ᴺᶠ-∘ :
  (a : Nf Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘' δ ]ᴺᶠ ≡ a [ γ ]ᴺᶠ [ δ ]ᴺᶠ

[]ᴺᵉ-∘ (var a) γ δ = λ i → var ([]-∘' a γ δ i)
[]ᴺᵉ-∘ (app f a) γ δ = λ i → app ([]ᴺᵉ-∘ f γ δ i) ([]ᴺᶠ-∘ a γ δ i)
[]ᴺᵉ-∘ (case t a b) γ δ = λ i → case ([]ᴺᵉ-∘ t γ δ i) ([]ᴺᶠ-∘ a (γ ↑') (δ ↑' ) i) ([]ᴺᶠ-∘ b (γ ↑') (δ ↑' ) i)
[]ᴺᵉ-∘ (exfalsoₗ a) γ δ = λ i → exfalsoₗ ([]ᴺᵉ-∘ a γ δ i)

[]ᴺᶠ-∘ (lam b) γ δ = λ i → lam ([]ᴺᶠ-∘ b (γ ↑') (δ ↑' ) i)
[]ᴺᶠ-∘ (+-ne a) γ δ = λ i → +-ne ([]ᴺᵉ-∘ a γ δ i) 
[]ᴺᶠ-∘ (⊥ₗ-ne a) γ δ = λ i → ⊥ₗ-ne ([]ᴺᵉ-∘ a γ δ i) 
[]ᴺᶠ-∘ (inlₗ a) γ δ = λ i → inlₗ ([]ᴺᶠ-∘ a γ δ i)
[]ᴺᶠ-∘ (inrₗ a) γ δ = λ i → inrₗ ([]ᴺᶠ-∘ a γ δ i)
[]ᴺᶠ-∘ ttₗ γ δ = refl



[]ᴺᵉ-id : (a : Ne Γ A) → a [ id' ]ᴺᵉ ≡ a
[]ᴺᶠ-id : (a : Nf Γ A) → a [ id' ]ᴺᶠ ≡ a

[]ᴺᵉ-id (var x) = λ i → var ([]-id' x i)
[]ᴺᵉ-id (app a x) = λ i → app ([]ᴺᵉ-id a i) ([]ᴺᶠ-id x i)
[]ᴺᵉ-id (case a x x₁) = λ i → case ([]ᴺᵉ-id a i) ([]ᴺᶠ-id x i) ([]ᴺᶠ-id x₁ i)
[]ᴺᵉ-id (exfalsoₗ a) = λ i → exfalsoₗ ([]ᴺᵉ-id a i)

[]ᴺᶠ-id (lam a) = λ i → lam ([]ᴺᶠ-id a i)
[]ᴺᶠ-id (+-ne x) = λ i → +-ne ([]ᴺᵉ-id x i)
[]ᴺᶠ-id (⊥ₗ-ne x) = λ i → ⊥ₗ-ne ([]ᴺᵉ-id x i)
[]ᴺᶠ-id (inlₗ a) = λ i → inlₗ ([]ᴺᶠ-id a i)
[]ᴺᶠ-id (inrₗ a) = λ i → inrₗ ([]ᴺᶠ-id a i)
[]ᴺᶠ-id ttₗ = λ i → ttₗ