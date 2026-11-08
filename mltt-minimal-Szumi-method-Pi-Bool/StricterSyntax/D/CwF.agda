{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D.CwF {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

open import Lib
open Iₛ

private module T = DepModel.DepModel T

open import D
open import InductionPrinciple D
open import Syntax
import Sorts as D'
open D'.Con∙
open D'.Sub∙
open D'.Ty∙
open D'.Tm∙

open import StricterSyntax.D.Sorts T

ICwF∙ : CwF∙ I ISorts∙
ICwF∙ = record
         { _∘∙_ = λ {Δ}{Δ∙}{Γ}{Γ∙}{γ}{Θ}{Θ∙}{δ} γ∙ δ∙ →
                  let
                    (γ∘δ ,-) = ∣ ⟦ γ ⟧Sub ∣ δ
                  in coe (cong T.Sub∙ₑ $ refl $ refl $ refl $ refl $ sym un) (γ∙ T.∘∙ δ∙)
         ; ass∙ = λ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙}{Ξ}{Ξ∙}{θ}{θ∙} →
                  let
                    (γ∘δ ,-) = ∣ ⟦ γ ⟧Sub ∣ δ
                    (δ∘θ ,-) = ∣ ⟦ δ ⟧Sub ∣ θ
                    proof = sym coh
                          ∙ cong T.∘∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ un $ refl $ sym coh $ refl
                          ∙ T.ass∙
                          ∙ cong T.∘∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ sym un $ refl $ coh
                          ∙ coh
                  in proof
         ; id∙ = T.id∙
         ; idl∙ = sym coh ∙ T.idl∙
         ; idr∙ = sym coh ∙ T.idr∙
         ; ◇∙ = T.◇∙
         ; ε∙ = T.ε∙
         ; ◇η∙ = T.◇η∙
         ; _[_]T∙ = λ {Γ}{Γ∙}{n}{A}{Δ}{Δ∙}{γ} A∙ γ∙ →
                    let
                      (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                    in coe (cong T.Ty∙ₑ $ refl $ refl $ refl $ sym un) (A∙ T.[ γ∙ ]T∙)
         ; [∘]T∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙} →
                   let
                     (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                     (γ∘δ ,-) = ∣ ⟦ γ ⟧Sub ∣ δ
                     proof = sym coh
                           ∙ cong T.[]T∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ un $ sym coh
                           ∙ T.[∘]T∙
                           ∙ cong T.[]T∙ₑ $ refl $ refl $ refl $ sym un $ refl $ refl $ coh $ refl $ refl
                           ∙ coh
                   in proof 
         ; [id]T∙ = sym coh ∙ T.[id]T∙
         ; _[_]t∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{a}{Δ}{Δ∙}{γ} a∙ γ∙ →
                    let
                      (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                      (a[γ]t ,-) = ∣ ⟦ a ⟧Tm ∣ γ
                    in coe (cong T.Tm∙ₑ $ refl $ refl $ sym un $ refl $ coh $ sym un) (a∙ T.[ γ∙ ]t∙)
         ; [∘]t∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙}{Θ}{δ}{Θ∙}{δ∙} →
                  let
                    (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                    (a[γ]t ,-) = ∣ ⟦ a ⟧Tm ∣ γ
                    (γ∘δ ,-) = ∣ ⟦ γ ⟧Sub ∣ δ
                    proof = sym coh
                          ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ un $ refl $ sym coh
                          ∙ T.[∘]t∙
                          ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ sym un $ coh $ sym un $ refl $ refl $ refl $ coh $ refl
                          ∙ coh
                  in proof
         ; [id]t∙ = sym coh ∙ T.[id]t∙
         ; _▹∙_ = T._▹∙_
         ; p∙ = T.p∙
         ; q∙ = λ {Γ}{Γ∙}{n}{A}{A∙} →
                let
                  (A[p]T ,-) = ∣ ⟦ A ⟧Ty ∣ (Iₛ.p {A = A})
                in coe (cong T.Tm∙ₑ $ refl $ refl $ sym un $ refl $ coh $ sym coh) (T.q∙ {A∙ = A∙})
         ; _⁺∙ = λ {Δ}{Δ∙}{Γ}{Γ∙}{γ}{n}{A}{A∙} γ∙ →
                 let
                   (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                 in coe (cong T.Sub∙ₑ $ (cong I.▹ₑ $ refl $ refl $ sym un) $ refl $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ refl $ sym coh) (T._⁺∙ {A∙ = A∙} γ∙)
         ; ∘⁺∙ = λ {Δ}{Δ∙}{Γ}{γ}{Γ∙}{γ∙}{Θ}{δ}{Θ∙}{δ∙}{n}{A}{A∙} →
                 let
                   (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                   (A[γ][δ]T ,-) = ∣ ⟦ A[γ]T ⟧Ty ∣ δ
                   (γ∘δ ,-) = ∣ ⟦ γ ⟧Sub ∣ δ
                 in sym coh
                  ∙ cong T.⁺∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ un $ sym coh
                  ∙ T.∘⁺∙
                  ∙ cong T.∘∙ₑ $ refl
                               $ refl
                               $ (cong I.▹ₑ $ refl $ refl $ sym un)
                               $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh)
                               $ (cong I.▹ₑ $ refl $ refl $ (sym un ∙ cong I.[]Tₑ $ refl $ refl $ refl $ sym un $ refl))
                               $ (cong T.▹∙ₑ $ refl $ refl $ refl $ (sym un ∙ cong I.[]Tₑ $ refl $ refl $ refl $ sym un $ refl) $ (cong T.[]T∙ₑ $ refl $ refl $ refl $ sym un $ refl $ refl $ coh $ refl $ refl ∙ coh))
                               $ sym coh
                               $ (sym coh ∙ cong I.⁺ₑ $ refl $ refl $ refl $ sym un $ refl)
                               $ coh
                               $ (cong T.⁺∙ₑ $ refl $ refl $ refl $ refl $ refl $ sym un $ coh $ refl $ refl ∙ coh)
                  ∙ coh
         ; id⁺∙ = sym coh ∙ T.id⁺∙
         ; ⟨_⟩∙ = T.⟨_⟩∙
         ; ⟨⟩∘∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙} →
                  let
                    (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                    (a[γ]t ,-) = ∣ ⟦ a ⟧Tm ∣ γ
                    proof = sym coh
                          ∙ T.⟨⟩∘∙
                          ∙ cong T.∘∙ₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ refl $ refl $ sym coh $ (cong I.⟨⟩ₑ $ refl $ refl $ sym un $ sym un) $ coh $ (cong T.⟨⟩∙ₑ $ refl $ refl $ refl $ sym un $ coh $ sym un $ coh)
                          ∙ coh
                  in proof
         ; p∘⁺∙ = λ {Δ}{Γ}{Γ∙}{γ}{Δ∙}{γ∙}{n}{A}{A∙} →
                  let
                    (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                    proof = sym coh
                          ∙ cong T.∘∙ₑ $ refl $ refl $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ (cong T.▹∙ₑ  $ refl $ refl $ refl $ un $ sym coh) $ refl $ coh $ refl $ sym coh
                          ∙ T.p∘⁺∙
                          ∙ cong T.∘∙ₑ $ refl $ refl $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ refl $ (cong I.pₑ $ refl $ refl $ sym un) $ refl $ (cong T.p∙ₑ $ refl $ refl $ refl $ sym un $ coh)
                          ∙ coh
                  in proof
         ; p∘⟨⟩∙ = sym coh ∙ T.p∘⟨⟩∙
         ; q[⁺]∙ = λ {Γ}{Γ∙}{Δ}{γ}{Δ∙}{γ∙}{n}{A}{A∙} →
                   let
                     (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                     (A[p]T ,-) = ∣ ⟦ A ⟧Ty ∣ (I.p {A = A})
                     proof = sym coh
                           ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ un $ sym coh $ coh $ (cong I.▹ₑ $ refl $ refl $ un) $ (cong T.▹∙ₑ $ refl $ refl $ refl $ un $ sym coh) $ coh $ sym coh $ sym coh
                           ∙ T.q[⁺]∙
                           ∙ cong T.q∙ₑ $ refl $ refl $ refl $ sym un $ coh
                           ∙ coh
                   in proof
         ; q[⟨⟩]∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙} →
                    let
                      (A[p]T ,-) = ∣ ⟦ A ⟧Ty ∣ (I.p {A = A})
                      proof = sym coh
                            ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ un $ sym coh $ coh $ refl $ refl $ refl $ sym coh $ refl
                            ∙ T.q[⟨⟩]∙
                    in proof
         ; ▹η∙ = λ {Γ}{Γ∙}{n}{A}{A∙} →
                 let
                   (A[p]T ,-) = ∣ ⟦ A ⟧Ty ∣ (I.p {A = A})
                   proof = T.▹η∙
                         ∙ cong T.∘∙ₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ refl $ refl $ sym coh $ (cong I.⟨⟩ₑ $ refl $ refl $ sym un $ sym coh) $ coh $ (cong T.⟨⟩∙ₑ $ refl $ refl $ refl $ sym un $ coh $ sym coh $ coh)
                         ∙ coh
                 in proof
         }
