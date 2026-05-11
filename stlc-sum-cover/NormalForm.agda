{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path
open import Cubical.Data.Sum hiding (map) renaming (inl to ⊎-inl; inr to ⊎-inr)
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ) hiding (assoc; id)
module stlc-sum-cover.NormalForm where
open import stlc-sum-cover.Syntax as S 
open import stlc-sum-cover.Weakening

private variable
  n : ℕ
  Γ Δ Θ : S.Con
  A B C P : S.Ty

data Ne : S.Con → S.Ty → Type
data Nf : S.Con → S.Ty → Type

data Ne where
  var : Var Γ A → Ne Γ A
  app : Ne Γ (A S.⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  lam : Nf (Γ S.▸ A) B → Nf Γ (A S.⇒ B)
  inl : Nf Γ A → Nf Γ (A S.+ B)
  inr : Nf Γ B → Nf Γ (A S.+ B)
  caseNe : ∀ {A B} → Ne Γ (A S.+ B) → Nf (Γ S.▸ A) P → Nf (Γ S.▸ B) P → Nf Γ P
  exfalsoNe : Ne Γ S.⊥ₗ → Nf Γ P

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

Nf-emb (lam a) = S.lam (Nf-emb a)
Nf-emb (inl a) = S.inl (Nf-emb a)
Nf-emb (inr b) = S.inr (Nf-emb b)
Nf-emb (caseNe ne c1 c2) = S.caseₗ (Ne-emb ne) (Nf-emb c1) (Nf-emb c2)
Nf-emb (exfalsoNe ne) = S.exfalsoₗ (Ne-emb ne)

infixl 40 _[_]ᴺᵉ _[_]ᴺᶠ
_[_]ᴺᵉ : Ne Γ A → Wk Δ Γ → Ne Δ A
_[_]ᴺᶠ : Nf Γ A → Wk Δ Γ → Nf Δ A

var a [ γ ]ᴺᵉ = var (a [ γ ]')
app f a [ γ ]ᴺᵉ = app (f [ γ ]ᴺᵉ) (a [ γ ]ᴺᶠ)

lam b [ γ ]ᴺᶠ = lam (b [ γ ↑' ]ᴺᶠ)
inl a [ γ ]ᴺᶠ = inl (a [ γ ]ᴺᶠ)
inr b [ γ ]ᴺᶠ = inr (b [ γ ]ᴺᶠ)
caseNe ne c1 c2 [ γ ]ᴺᶠ = caseNe (ne [ γ ]ᴺᵉ) (c1 [ γ ↑' ]ᴺᶠ) (c2 [ γ ↑' ]ᴺᶠ)
exfalsoNe ne [ γ ]ᴺᶠ = exfalsoNe (ne [ γ ]ᴺᵉ)

Ne-emb-[] :
  (a : Ne Γ A) (γ : Wk Δ Γ) → Ne-emb (a [ γ ]ᴺᵉ) ≡ Ne-emb a S.[ Wk-emb γ ]
Nf-emb-[] :
  (a : Nf Γ A) (γ : Wk Δ Γ) → Nf-emb (a [ γ ]ᴺᶠ) ≡ Nf-emb a S.[ Wk-emb γ ]

Ne-emb-[] (var x) γ = Var-emb-[] _ _
Ne-emb-[] (app f a) γ = (λ i → app (Ne-emb-[] f γ i) (Nf-emb-[] a γ i)) ∙ sym (S.app-[] (Ne-emb f) (Nf-emb a) (Wk-emb γ))

Nf-emb-[] (lam a) γ = (λ i → lam (Nf-emb-[] a (γ ↑') i)) ∙ sym (S.lam-[] (Nf-emb a) (Wk-emb γ))
Nf-emb-[] (inl a) γ = (λ i → S.inl (Nf-emb-[] a γ i)) ∙ sym (S.inl-[] (Nf-emb a) (Wk-emb γ))
Nf-emb-[] (inr b) γ = (λ i → S.inr (Nf-emb-[] b γ i)) ∙ sym (S.inr-[] (Nf-emb b) (Wk-emb γ))
Nf-emb-[] (caseNe ne c1 c2) γ = (λ i → S.caseₗ (Ne-emb-[] ne γ i) (Nf-emb-[] c1 (γ ↑') i) (Nf-emb-[] c2 (γ ↑') i)) ∙ sym (S.caseₗ-[] (Ne-emb ne) (Nf-emb c1) (Nf-emb c2) (Wk-emb γ))
Nf-emb-[] (exfalsoNe ne) γ = (λ i → S.exfalsoₗ (Ne-emb-[] ne γ i)) ∙ sym (S.exfalsoₗ-[] (Ne-emb ne) (Wk-emb γ))

[]ᴺᵉ-∘ :
  (a : Ne Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘' δ ]ᴺᵉ ≡ a [ γ ]ᴺᵉ [ δ ]ᴺᵉ
[]ᴺᶠ-∘ :
  (a : Nf Γ A) (γ : Wk Δ Γ) (δ : Wk Θ Δ) → a [ γ ∘' δ ]ᴺᶠ ≡ a [ γ ]ᴺᶠ [ δ ]ᴺᶠ

[]ᴺᵉ-∘ (var a) γ δ = λ i → var ([]-∘' a γ δ i)
[]ᴺᵉ-∘ (app f a) γ δ = λ i → app ([]ᴺᵉ-∘ f γ δ i) ([]ᴺᶠ-∘ a γ δ i)

[]ᴺᶠ-∘ (lam b) γ δ = λ i → lam ([]ᴺᶠ-∘ b (γ ↑') (δ ↑' ) i)
[]ᴺᶠ-∘ (inl a) γ δ = λ i → inl ([]ᴺᶠ-∘ a γ δ i)
[]ᴺᶠ-∘ (inr b) γ δ = λ i → inr ([]ᴺᶠ-∘ b γ δ i)
[]ᴺᶠ-∘ (caseNe ne c1 c2) γ δ = λ i → caseNe ([]ᴺᵉ-∘ ne γ δ i) ([]ᴺᶠ-∘ c1 (γ ↑') (δ ↑') i) ([]ᴺᶠ-∘ c2 (γ ↑') (δ ↑') i)
[]ᴺᶠ-∘ (exfalsoNe a) γ δ = λ i → exfalsoNe ([]ᴺᵉ-∘ a γ δ i)


[]ᴺᵉ-id : (a : Ne Γ A) → a [ id' ]ᴺᵉ ≡ a
[]ᴺᶠ-id : (a : Nf Γ A) → a [ id' ]ᴺᶠ ≡ a

[]ᴺᵉ-id (var x) = λ i → var ([]-id' x i)
[]ᴺᵉ-id (app a x) = λ i → app ([]ᴺᵉ-id a i) ([]ᴺᶠ-id x i)

[]ᴺᶠ-id (lam a) = λ i → lam ([]ᴺᶠ-id a i)
[]ᴺᶠ-id (inl a) = λ i → inl ([]ᴺᶠ-id a i)
[]ᴺᶠ-id (inr b) = λ i → inr ([]ᴺᶠ-id b i)
[]ᴺᶠ-id (caseNe ne c1 c2) = λ i → caseNe ([]ᴺᵉ-id ne i) ([]ᴺᶠ-id c1 i) ([]ᴺᶠ-id c2 i)
[]ᴺᶠ-id (exfalsoNe a) = λ i → exfalsoNe ([]ᴺᵉ-id a i)


data _≤_ : S.Ty → S.Ty → Type where
  refl≤  : A ≤ A
  left⇒  : A ≤ B → A ≤ (B S.⇒ C)
  right⇒ : A ≤ C → A ≤ (B S.⇒ C)
  left+  : A ≤ B → A ≤ (B S.+ C)
  right+ : A ≤ C → A ≤ (B S.+ C)

trans≤ : A ≤ B → B ≤ C → A ≤ C
trans≤ r refl≤    = r
trans≤ r (left⇒  s) = left⇒  (trans≤ r s)
trans≤ r (right⇒ s) = right⇒ (trans≤ r s)
trans≤ r (left+  s) = left+  (trans≤ r s)
trans≤ r (right+ s) = right+ (trans≤ r s)

A≤A⇒B : A ≤ (A S.⇒ B)
A≤A⇒B = left⇒ refl≤

B≤A⇒B : B ≤ (A S.⇒ B)
B≤A⇒B = right⇒ refl≤

A≤A+B : A ≤ (A S.+ B) 
A≤A+B = left+ refl≤

B≤A+B : B ≤ (A S.+ B) 
B≤A+B = right+ refl≤

data _∈Γ≤_ (A : S.Ty) : S.Con → Type where
  here-≤  : A ≤ B     → A ∈Γ≤ (Γ S.▸ B)  
  there-≤ : A ∈Γ≤ Γ  → A ∈Γ≤ (Γ S.▸ B)  

Var→∈Γ≤ : Var Γ A → A ∈Γ≤ Γ
Var→∈Γ≤ q       = here-≤ refl≤   
Var→∈Γ≤ (v [p]) = there-≤ (Var→∈Γ≤ v)
  
≤-∈Γ≤ : A ≤ B → B ∈Γ≤ Γ → A ∈Γ≤ Γ
≤-∈Γ≤ x (here-≤ x₁) = here-≤ (trans≤ x x₁)
≤-∈Γ≤ x (there-≤ e) = there-≤ (≤-∈Γ≤ x e)  

Ne-sfp : (ne : Ne Γ A) → A ∈Γ≤ Γ
Ne-sfp (var x)   = Var→∈Γ≤ x
Ne-sfp (app f a) = ≤-∈Γ≤ B≤A⇒B (Ne-sfp f)


exfalsoNe-scrut-∈Γ≤ : (ne : Ne Γ S.⊥ₗ) → S.⊥ₗ ∈Γ≤ Γ
exfalsoNe-scrut-∈Γ≤ ne = Ne-sfp ne


data _∈Ne_ (B : S.Ty) : {Γ : S.Con} {A : S.Ty} → Ne Γ A → Type
data _∈Nf_ (B : S.Ty) : {Γ : S.Con} {A : S.Ty} → Nf Γ A → Type

data _∈Ne_ B where
  self-Ne  : {Γ : S.Con} {ne : Ne Γ B} → B ∈Ne ne
  in-fun   : {Γ : S.Con} {X C : S.Ty} {f : Ne Γ (X S.⇒ C)} {a : Nf Γ X}
           → B ∈Ne f → B ∈Ne app f a
  in-arg   : {Γ : S.Con} {X C : S.Ty} {f : Ne Γ (X S.⇒ C)} {a : Nf Γ X}
           → B ∈Nf a → B ∈Ne app f a

data _∈Nf_ B where
  in-lam-body : {Γ : S.Con} {X C : S.Ty} {b : Nf (Γ S.▸ X) C}
              → B ∈Nf b → B ∈Nf lam b
  in-inl      : {Γ : S.Con} {X Y : S.Ty} {a : Nf Γ X}
              → B ∈Nf a → B ∈Nf inl {B = Y} a
  in-inr      : {Γ : S.Con} {X Y : S.Ty} {b : Nf Γ Y}
              → B ∈Nf b → B ∈Nf inr {A = X} b
  in-case-ne  : {Γ : S.Con} {X Y P' : S.Ty}
                {ne : Ne Γ (X S.+ Y)} {c1 : Nf (Γ S.▸ X) P'} {c2 : Nf (Γ S.▸ Y) P'}
              → B ∈Ne ne → B ∈Nf caseNe ne c1 c2
  in-case-c1  : {Γ : S.Con} {X Y P' : S.Ty}
                {ne : Ne Γ (X S.+ Y)} {c1 : Nf (Γ S.▸ X) P'} {c2 : Nf (Γ S.▸ Y) P'}
              → B ∈Nf c1 → B ∈Nf caseNe ne c1 c2
  in-case-c2  : {Γ : S.Con} {X Y P' : S.Ty}
                {ne : Ne Γ (X S.+ Y)} {c1 : Nf (Γ S.▸ X) P'} {c2 : Nf (Γ S.▸ Y) P'}
              → B ∈Nf c2 → B ∈Nf caseNe ne c1 c2
  in-exf      : {Γ : S.Con} {P' : S.Ty} {ne : Ne Γ S.⊥ₗ}
              → B ∈Ne ne → B ∈Nf exfalsoNe {P = P'} ne

mutual
  Ne-sfp-complete : {Γ : S.Con} {A : S.Ty} (ne : Ne Γ A)
                  → B ∈Ne ne → B ∈Γ≤ Γ
  Ne-sfp-complete (var x)   self-Ne    = Var→∈Γ≤ x
  Ne-sfp-complete (app f a) self-Ne    = ≤-∈Γ≤ B≤A⇒B (Ne-sfp f)
  Ne-sfp-complete (app f a) (in-fun x) = Ne-sfp-complete f x
  Ne-sfp-complete (app {A = X} f a) (in-arg x) with Nf-sfp-complete a x
  ... | ⊎-inl B≤X    = ≤-∈Γ≤ (trans≤ B≤X A≤A⇒B) (Ne-sfp f)
  ... | ⊎-inr B∈Γ≤   = B∈Γ≤

  Nf-sfp-complete : {Γ : S.Con} {A : S.Ty} (nf : Nf Γ A)
                  → B ∈Nf nf → (B ≤ A) ⊎ (B ∈Γ≤ Γ)
  Nf-sfp-complete (lam {A = X} b)          (in-lam-body x)
    with Nf-sfp-complete b x
  ... | ⊎-inl B≤C               = ⊎-inl (trans≤ B≤C B≤A⇒B)
  ... | ⊎-inr (here-≤ B≤X)      = ⊎-inl (trans≤ B≤X A≤A⇒B)
  ... | ⊎-inr (there-≤ B∈Γ≤)   = ⊎-inr B∈Γ≤
  Nf-sfp-complete (inl {B = Y} a)          (in-inl x)
    with Nf-sfp-complete a x
  ... | ⊎-inl B≤X    = ⊎-inl (trans≤ B≤X A≤A+B)
  ... | ⊎-inr B∈Γ≤   = ⊎-inr B∈Γ≤
  Nf-sfp-complete (inr {A = X} b)          (in-inr x)
    with Nf-sfp-complete b x
  ... | ⊎-inl B≤Y    = ⊎-inl (trans≤ B≤Y B≤A+B)
  ... | ⊎-inr B∈Γ≤   = ⊎-inr B∈Γ≤
  Nf-sfp-complete (caseNe ne c1 c2)        (in-case-ne x)
    = ⊎-inr (Ne-sfp-complete ne x)
  Nf-sfp-complete (caseNe {A = X} {B = Y} ne c1 c2) (in-case-c1 x)
    with Nf-sfp-complete c1 x
  ... | ⊎-inl B≤P               = ⊎-inl B≤P
  ... | ⊎-inr (here-≤ B≤X)      = ⊎-inr (≤-∈Γ≤ (trans≤ B≤X A≤A+B) (Ne-sfp ne))
  ... | ⊎-inr (there-≤ B∈Γ≤)   = ⊎-inr B∈Γ≤
  Nf-sfp-complete (caseNe {A = X} {B = Y} ne c1 c2) (in-case-c2 x)
    with Nf-sfp-complete c2 x
  ... | ⊎-inl B≤P               = ⊎-inl B≤P
  ... | ⊎-inr (here-≤ B≤Y)      = ⊎-inr (≤-∈Γ≤ (trans≤ B≤Y B≤A+B) (Ne-sfp ne))
  ... | ⊎-inr (there-≤ B∈Γ≤)   = ⊎-inr B∈Γ≤
  Nf-sfp-complete (exfalsoNe ne)            (in-exf x)
    = ⊎-inr (Ne-sfp-complete ne x)