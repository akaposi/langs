{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ) hiding (assoc; id; isoToEquiv; _≃_; ua)
module stlc-sum.Norm where
open import stlc-sum.test as T
open import stlc-sum.DepModel as D
open import stlc-sum.Syntax as S 
open import stlc-sum.InitialModel
open import stlc-sum.Weakening as W
open import stlc-sum.NormalForm as N

import stlc-sum.Induction as I

Normalize : D.DepModel In 
Normalize .DepModel.Con∙ = T.test.Con
Normalize .DepModel.Sub∙ = T.test.Sub
Normalize .DepModel.SubSet∙ = T.test.isSetSub _ _ _ 
Normalize .DepModel._∘∙_ = T.test._∘_
Normalize .DepModel.assoc∙ = T.test.assoc
Normalize .DepModel.id∙ = T.test.id
Normalize .DepModel.idr∙ = T.test.idr
Normalize .DepModel.idl∙ = T.test.idl
Normalize .DepModel.Ty∙ = T.test.Ty
Normalize .DepModel.Tm∙ = T.test.Tm
Normalize .DepModel.TmSet∙ = T.test.isSetTm _ _ _ 
Normalize .DepModel._[_]∙ = T.test._[_]
Normalize .DepModel.[]-∘∙ = T.test.[]-∘
Normalize .DepModel.[]-id∙ = T.test.[]-id
Normalize .DepModel._▸∙_ = T.test._▸_
Normalize .DepModel.p∙ = T.test.p
Normalize .DepModel.q∙ = T.test.q
Normalize .DepModel._,∙_ = T.test._,_ₛ
Normalize .DepModel.,-∘∙ = T.test.,-∘
Normalize .DepModel.▸-β₁∙ = T.test.▸-β₁
Normalize .DepModel.▸-β₂∙ = T.test.▸-β₂
Normalize .DepModel.▸-η∙ = T.test.▸-η
Normalize .DepModel.◆∙ = T.test.◆
Normalize .DepModel.ε∙ = T.test.ε
Normalize .DepModel.ε-∘∙ = T.test.ε-∘
Normalize .DepModel.◆-η∙ = T.test.◆-η
Normalize .DepModel._⇒∙_ = T.test._⇒_
Normalize .DepModel._+ₗ∙_ = T.test._+ₗ_
Normalize .DepModel.app∙ = T.test.app
Normalize .DepModel.app-[]∙ = T.test.app-[]
Normalize .DepModel.lam∙ = T.test.lam
Normalize .DepModel.lam-[]∙ = T.test.lam-[]
Normalize .DepModel.⇒-β∙ = T.test.⇒-β
Normalize .DepModel.⇒-η∙ = T.test.⇒-η
Normalize .DepModel.⊥ₗ∙ = T.test.⊥ₗ
Normalize .DepModel.exfalsoₗ∙ = T.test.exfalsoₗ
Normalize .DepModel.exfalsoₗ-[]∙ = T.test.exfalsoₗ-[]
Normalize .DepModel.Unitₗ∙ = T.test.Unitₗ
Normalize .DepModel.ttₗ∙ = T.test.ttₗ
Normalize .DepModel.ttₗ-[]∙ = T.test.ttₗ-[]
Normalize .DepModel.unit-η∙ = T.test.unit-η
Normalize .DepModel.inlₗ∙ = T.test.inlₗ
Normalize .DepModel.inlₗ-[]∙ = T.test.inlₗ-[]
Normalize .DepModel.inrₗ∙ = T.test.inrₗ
Normalize .DepModel.inrₗ-[]∙ = T.test.inrₗ-[]
Normalize .DepModel.case+∙ = T.test.case+
Normalize .DepModel.case+[]∙ = T.test.case+[]
Normalize .DepModel.+-β₁∙ = T.test.+-β₁
Normalize .DepModel.+-β₂∙ = T.test.+-β₂

open module NormInduction = I Normalize

private variable
  Γ : S.Con
  A A₁ : S.Ty

ref-id : ∀ Γ → fst (T.test.Con.∣_∣ ⟦ Γ ⟧Cᵢ Γ)
ref-id (Γ ▸ A) =  (⟦ Γ ⟧Cᵢ test.! (ref-id Γ) [ (W.id' W.∘p) ]) , (⟦ A ⟧Tᵢ .test.ref (N.var W.q)) 
ref-id ◆ = tt

map-ref-id : ∀ Γ → ⟦ Γ ⟧Cᵢ .test.map (ref-id Γ) ≡ S.id
map-ref-id (Γ ▸ A) =  ((λ i → ⟦ Γ ⟧Cᵢ .test.map-[] (ref-id Γ) (W.id' W.∘p) i , ⟦ A ⟧Tᵢ .test.map-ref (N.var W.q) i)) ∙  ((λ i → map-ref-id Γ i S.∘ (Wk-emb id' ∘ p) , q)) ∙ (λ i → ( S.idl (Wk-emb id' ∘ p) i  , q)) ∙ (λ i → (Wk-emb-id i  ∘ p , ⟦ A ⟧Tᵢ .test.map-ref (N.var W.q) (~ i))) ∙ (λ i → (S.idl p i ,  ⟦ A ⟧Tᵢ .test.map-ref (N.var W.q) i)) ∙ S.▸-η
map-ref-id ◆ = S.◆-η

reflect : S.Tm Γ A → fst (test.Ty.∣_∣ ⟦ A ⟧Tᵢ Γ)
reflect {Γ} a = test.∣ ⟦ a ⟧tᵢ ∣ (ref-id Γ)

normalize : S.Tm Γ A → Nf Γ A
normalize {A = A} a = ⟦ A ⟧Tᵢ .test.quo (reflect a)

completeness : (a : S.Tm Γ A) → Nf-emb (normalize a) ≡ a
completeness {Γ} {A} a = (test.Ty.emb-quo ⟦ A ⟧Tᵢ _ ∙ test.Tm.map ⟦ a ⟧tᵢ _) ∙ (λ i → a [ map-ref-id _ i ]) ∙  S.[]-id _

Var-stability : (a : Var Γ A) → reflect (Var-emb a) ≡ ⟦ A ⟧Tᵢ .test.ref (N.var a)
Var-stability q = refl
Var-stability {A = A}(a [p]) = ⟦  (Var-emb a) ⟧tᵢ .test.![] _ _ ∙ (λ i → ⟦ A ⟧Tᵢ test.! (Var-stability a i) [ (W.id' W.∘p) ]) ∙ sym (⟦ A ⟧Tᵢ .test.ref-[] _ _) ∙ λ i → test.ref ⟦ A ⟧Tᵢ (N.var ([]-id' a i [p]))

Ne-stability : (a : Ne Γ A) → reflect (Ne-emb a) ≡ ⟦ A ⟧Tᵢ .test.ref a
Nf-stability : (a : Nf Γ A) → normalize (Nf-emb a) ≡ a

Ne-stability (var a) = Var-stability a
Ne-stability (app {B = B} f a) = (λ i → Ne-stability f i .test.sem W.id' (reflect (Nf-emb a))) ∙ (λ i → test.ref ⟦ B ⟧Tᵢ (app ([]ᴺᵉ-id f i) (normalize (Nf-emb a)) )) ∙ λ i →  test.ref ⟦ B ⟧Tᵢ (app f (Nf-stability a i))
Ne-stability {Γ = Γ} {A = C} (case  {A = A} {B = B} s a b )  = 
    (λ i → test.case+-sem ⟦ A ⟧Tᵢ ⟦ B ⟧Tᵢ ⟦ C ⟧Tᵢ 
           (Ne-stability s i) 
           (λ x a₁ → test.∣ ⟦ Nf-emb a ⟧tᵢ ∣ (⟦ Γ ⟧Cᵢ test.! ref-id Γ [ x ] , a₁)) 
           (λ x b₁ → test.∣ ⟦ Nf-emb b ⟧tᵢ ∣ (⟦ Γ ⟧Cᵢ test.! ref-id Γ [ x ] , b₁))) 
    ∙ (λ i → test.ref ⟦ C ⟧Tᵢ (case s (normalize (Nf-emb a)) (normalize (Nf-emb b))))
    ∙ (λ i → test.ref ⟦ C ⟧Tᵢ (case s (Nf-stability a i) (Nf-stability b i)))
Ne-stability (exfalsoₗ {A = A} a) = λ i → test.exfalso-sem (⟦ A ⟧Tᵢ) (Ne-stability a i)

Nf-stability (lam b) = λ i → lam (Nf-stability b i)
Nf-stability {A = A S.+ₗ B}(+-ne x) = λ i → test.quo (⟦ A ⟧Tᵢ test.+ₗ ⟦ B ⟧Tᵢ) (Ne-stability x i)
Nf-stability (⊥ₗ-ne x) = λ i → test.quo ⟦ S.⊥ₗ ⟧Tᵢ (Ne-stability x i)
Nf-stability (inlₗ a) = λ i → inlₗ (Nf-stability a i)
Nf-stability (inrₗ b) = λ i → inrₗ (Nf-stability b i)
Nf-stability ttₗ = refl

Tm≃Nf : S.Tm Γ A ≃ N.Nf Γ A
Tm≃Nf {A = A } = isoToEquiv (iso normalize Nf-emb  Nf-stability completeness)

Discrete-Tm : Discrete (S.Tm Γ A)
Discrete-Tm = subst Discrete (sym (ua Tm≃Nf)) discreteNf

module Example {Γ : S.Con} where
  Boolₑ : S.Ty
  Boolₑ = S.Unitₗ S.+ₗ S.Unitₗ

  t1 : S.Tm Γ (Boolₑ S.⇒ Boolₑ)
  t1 = S.lam S.q

  t2 : S.Tm Γ (Boolₑ S.⇒ Boolₑ)
  t2 = S.lam (S.case+ S.q (S.inlₗ S.ttₗ) (S.inrₗ S.ttₗ))

  Dist : N.Nf Γ (Boolₑ S.⇒ Boolₑ) → Type
  Dist (N.lam (N.+-ne (N.var _))) = Unit
  Dist _                          = ⊥

  t1≢t2 : ¬ (t1 ≡ t2)
  t1≢t2 x = 
    let
      x-nf : normalize t1 ≡ normalize t2
      x-nf = cong normalize x
    in 
      (subst Dist x-nf tt)
  