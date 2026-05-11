{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}

module stlc-sum-cover.Norm where
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Path

import stlc-sum-cover.Syntax as S
import stlc-sum-cover.Weakening as W
import stlc-sum-cover.NormalForm as N
import stlc-sum-cover.Normalization as Norm
import stlc-sum-cover.Cover as Co

import stlc-sum-cover.InitialModel as I
import stlc-sum-cover.DepModel as Dep
import stlc-sum-cover.Induction as Ind

private variable
  Γ Δ : S.Con
  A B : S.Ty

NormModel : Dep.DepModel I.In 
NormModel .Dep.DepModel.Con∙ = Norm.Con
NormModel .Dep.DepModel.Sub∙ = Norm.Sub
NormModel .Dep.DepModel.SubSet∙ = Norm.isSetSub _ _ _ 
NormModel .Dep.DepModel._∘∙_ = Norm._∘_
NormModel .Dep.DepModel.assoc∙ = Norm.assoc
NormModel .Dep.DepModel.id∙ = Norm.id
NormModel .Dep.DepModel.idr∙ = Norm.idr
NormModel .Dep.DepModel.idl∙ = Norm.idl
NormModel .Dep.DepModel.Ty∙ = Norm.Ty
NormModel .Dep.DepModel.Tm∙ = Norm.Tm
NormModel .Dep.DepModel.TmSet∙ = Norm.isSetTm _ _ _
NormModel .Dep.DepModel._[_]∙ = Norm._[_]
NormModel .Dep.DepModel.[]-∘∙ = Norm.[]-∘
NormModel .Dep.DepModel.[]-id∙ = Norm.[]-id
NormModel .Dep.DepModel._▸∙_ = Norm._▸_
NormModel .Dep.DepModel.p∙ = Norm.p
NormModel .Dep.DepModel.q∙ = Norm.q
NormModel .Dep.DepModel._,∙_ = Norm._,_ₛ
NormModel .Dep.DepModel.,-∘∙ = Norm.,-∘
NormModel .Dep.DepModel.▸-β₁∙ = Norm.▸-β₁
NormModel .Dep.DepModel.▸-β₂∙ = Norm.▸-β₂
NormModel .Dep.DepModel.▸-η∙ = Norm.▸-η
NormModel .Dep.DepModel.◆∙ = Norm.◆
NormModel .Dep.DepModel.ε∙ = Norm.ε
NormModel .Dep.DepModel.ε-∘∙ = Norm.ε-∘
NormModel .Dep.DepModel.◆-η∙ = Norm.◆-η
NormModel .Dep.DepModel._⇒∙_ = Norm._⇒_
NormModel .Dep.DepModel.app∙ = Norm.app
NormModel .Dep.DepModel.app-[]∙ = Norm.app-[]
NormModel .Dep.DepModel.lam∙ = Norm.lam
NormModel .Dep.DepModel.lam-[]∙ = Norm.lam-[]
NormModel .Dep.DepModel.⇒-β∙ = Norm.⇒-β
NormModel .Dep.DepModel.⇒-η∙ = Norm.⇒-η
NormModel .Dep.DepModel.⊥ₗ∙ = Norm.⊥ₗ
NormModel .Dep.DepModel.exfalsoₗ∙ = Norm.exfalsoₗ
NormModel .Dep.DepModel.exfalsoₗ-[]∙ = Norm.exfalsoₗ-[]
NormModel .Dep.DepModel.⊥ₗ-η∙ = Norm.⊥ₗ-η
NormModel .Dep.DepModel.π-⇒0∙ = Norm.π-⇒0
NormModel .Dep.DepModel._+∙_ = Norm._+ₛ_
NormModel .Dep.DepModel.inl∙ = Norm.inlₛ
NormModel .Dep.DepModel.inl-[]∙ = Norm.inl-[]ₛ
NormModel .Dep.DepModel.inr∙ = Norm.inrₛ
NormModel .Dep.DepModel.inr-[]∙ = Norm.inr-[]ₛ
NormModel .Dep.DepModel.caseₗ∙ = Norm.caseₗₛ
NormModel .Dep.DepModel.caseₗ-[]∙ = Norm.caseₗ-[]ₛ
NormModel .Dep.DepModel.+-β₁∙ = Norm.+-β₁ₛ
NormModel .Dep.DepModel.+-β₂∙ = Norm.+-β₂ₛ
NormModel .Dep.DepModel.+-η∙ = Norm.+-ηₛ
NormModel .Dep.DepModel.π-+⇒∙ = Norm.π-+⇒ₛ
NormModel .Dep.DepModel.π-+0∙ = Norm.π-+0ₛ
NormModel .Dep.DepModel.π-++∙ = Norm.π-++ₛ
NormModel .Dep.DepModel.π-⇒+∙ = Norm.π-⇒+ₛ

module Eval = Ind NormModel
open Eval using (⟦_⟧Cᵢ; ⟦_⟧Tᵢ; ⟦_⟧Sᵢ; ⟦_⟧tᵢ)

ref-id : ∀ Γ → fst (Norm.Con.∣ ⟦ Γ ⟧Cᵢ ∣ Γ)
ref-id (Γ S.▸ A) = (⟦ Γ ⟧Cᵢ Norm.! ((ref-id Γ)) [ (W.id' W.∘p) ]) , Norm.Ty.ref ⟦ A ⟧Tᵢ (N.var W.q)
ref-id S.◆ = tt

map-ref-id : ∀ Γ → ⟦ Γ ⟧Cᵢ .Norm.map (ref-id Γ) ≡ S.id
map-ref-id (Γ S.▸ A) = ((((((λ i → ⟦ Γ ⟧Cᵢ .Norm.map-[] (ref-id Γ) (W.id' W.∘p) i S., ⟦ A ⟧Tᵢ .Norm.map-ref (N.var W.q) i))) ∙  ((λ i → map-ref-id Γ i S.∘ (W.Wk-emb W.id' S.∘ S.p) S., S.q)) ∙ (λ i → ( S.idl (W.Wk-emb W.id'  S.∘ S.p) i  S., S.q))) ∙  (λ i → (W.Wk-emb-id i  S.∘ S.p S., ⟦ A ⟧Tᵢ .Norm.map-ref (N.var W.q) (~ i)))) ∙ (λ i → (S.idl S.p i S.,  ⟦ A ⟧Tᵢ .Norm.map-ref (N.var W.q) i))) ∙ S.▸-η --{! ((λ i → ⟦ Γ ⟧Cᵢ .Norm.map-[] (ref-id Γ) (W.id' W.∘p) i , ⟦ A ⟧Tᵢ .Norm.map-ref (N.var W.q) i))  ∙ ?!}
map-ref-id S.◆ = S.◆-η

reflect : S.Tm Γ A → fst (Norm.Ty.∣_∣ ⟦ A ⟧Tᵢ Γ)
reflect {Γ} a = Norm.∣ ⟦ a ⟧tᵢ ∣ (ref-id Γ)

normalize : S.Tm Γ A → N.Nf Γ A
normalize {A = A} a = Co.runNf (⟦ A ⟧Tᵢ .Norm.quo (reflect a))

completeness : (a : S.Tm Γ A) → N.Nf-emb (normalize a) ≡ a
completeness {Γ} {A} a = Co.emb-runNf (⟦ A ⟧Tᵢ .Norm.quo (reflect a)) ∙ (Norm.Ty.emb-quo ⟦ A ⟧Tᵢ _ ∙ Norm.Tm.map ⟦ a ⟧tᵢ _) ∙ (λ i → a S.[ map-ref-id _ i ]) ∙ S.[]-id _


Var-stability : (a : W.Var Γ A) → reflect (W.Var-emb a) ≡ ⟦ A ⟧Tᵢ .Norm.ref (N.var a)
Var-stability W.q = refl
Var-stability {A = A} (a W.[p]) = ⟦  (W.Var-emb a) ⟧tᵢ .Norm.![] _ _ ∙ (λ i → ⟦ A ⟧Tᵢ Norm.! (Var-stability a i) [ (W.id' W.∘p) ]) ∙ sym (⟦ A ⟧Tᵢ .Norm.ref-[] _ _) ∙ λ i → Norm.ref ⟦ A ⟧Tᵢ (N.var (W.[]-id' a i W.[p]))

Ne-stability : (a : N.Ne Γ A) → reflect (N.Ne-emb a) ≡ ⟦ A ⟧Tᵢ .Norm.ref a
Nf-stability : (a : N.Nf Γ A) → normalize (N.Nf-emb a) ≡ a

Ne-stability (N.var a) = Var-stability a
Ne-stability (N.app {A = A} {B = B} f a) =  ((λ i →  Norm.appCov (Co.return (Ne-stability f i)) (reflect (N.Nf-emb a))) ∙  (λ i → Norm.ref ⟦ B ⟧Tᵢ (N.app (N.[]ᴺᵉ-id f i) (Co.runNf (Norm.quo ⟦ A ⟧Tᵢ (reflect (N.Nf-emb a))))))) ∙ λ i → Norm.ref ⟦ B ⟧Tᵢ (N.app f (Nf-stability a i)) 

Nf-stability (N.lam {A = A} {B = B} b) = Co.collapseNf-runNf (Norm.quo ⟦ B ⟧Tᵢ (reflect (N.Nf-emb b))) ∙ cong N.lam (Nf-stability b)
Nf-stability (N.exfalsoNe a) = {!  λ i → Norm.quo ? (Ne-stability a i) !} 
Nf-stability (N.caseNe ne c1 c2) = {!   !}  
Nf-stability (N.inl a) = cong N.inl (Nf-stability a)
Nf-stability (N.inr b) = cong N.inr (Nf-stability b)

Tm≃Nf : ∀ {Γ A} → S.Tm Γ A ≃ N.Nf Γ A
Tm≃Nf = isoToEquiv (iso normalize N.Nf-emb Nf-stability completeness)

Discrete-Tm : ∀ {Γ A} → Discrete (S.Tm Γ A)
Discrete-Tm {Γ} {A} = subst Discrete (sym (ua Tm≃Nf)) N.discreteNf


module Example {Γ : S.Con} {A B : S.Ty} where
  
  t1 : S.Tm (Γ S.▸ S.⊥ₗ) A 
  t1 = S.exfalsoₗ S.q 

  t2 : S.Tm (Γ S.▸ S.⊥ₗ) A 
  t2 = S.exfalsoₗ (S.exfalsoₗ S.q)

  t3 : S.Tm (Γ S.▸ S.⊥ₗ) (A S.⇒ B)
  t3 = S.exfalsoₗ S.q 
  
  t4 : S.Tm (Γ S.▸ S.⊥ₗ) (A S.⇒ B)
  t4 = S.lam (S.exfalsoₗ (S.q S.[ S.p ]))

  eq-t1t2 : normalize t1 ≡ normalize t2
  eq-t1t2 = refl

  eq-t3t4 : normalize t3 ≡ normalize t4
  eq-t3t4 = refl

  t5 : S.Tm (Γ S.▸ (A S.+ B)) (A S.+ B)
  t5 = S.caseₗ S.q (S.inl S.q) (S.inr S.q)

  t6 : S.Tm (Γ S.▸ (A S.+ B)) (A S.+ B)
  t6 = S.q

  eq-t5t6 : normalize t5 ≡ normalize t6
  eq-t5t6 = refl