{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D.Pi {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

open import Lib
open import Syntax
open import D
open import InductionPrinciple D

import Sorts as D'
open D'.Con∙
open D'.Sub∙
open D'.Ty∙
open D'.Tm∙

private module T = DepModel.DepModel T

open import StricterSyntax.D.Sorts T
open import StricterSyntax.D.CwF T

IPi∙ : Pi∙ I ISorts∙ ICwF∙
IPi∙ = record
        { Π∙ = T.Π∙
        ; Π[]∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{Δ}{Δ∙}{γ}{γ∙} →
                 let
                   (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                   (B[γ⁺]T ,-) = ∣ ⟦ B ⟧Ty ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺))
                 in sym coh ∙ T.Π[]∙ ∙ cong T.Π∙ₑ $ refl $ refl $ refl $ sym un $ coh $ (sym un ∙ cong I.[]Tₑ $ refl $ refl $ (cong (Δ I.▹_) $ sym un) $ refl $ sym coh) $ (cong T.[]T∙ₑ $ (cong (Δ I.▹_) $ sym un) $ refl $ refl $ refl $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ refl $ refl $ sym coh $ coh ∙ coh)
        ; lam∙ = T.lam∙
        ; app∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{f}{a} f∙ a∙ →
                 let
                   (B[a]T ,-) = ∣ ⟦ B ⟧Ty ∣ I.⟨ a ⟩
                 in coe (cong T.Tm∙ₑ $ refl $ refl $ sym un $ refl $ coh $ sym coh) (T.app∙ f∙ a∙)
        ; Πβ∙ = sym coh ∙ T.Πβ∙ ∙ coh
        ; Πη∙ = λ {Γ}{n}{Γ∙}{A}{B}{f}{A∙}{B∙}{f∙} →
                let
                  (A[p]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.p
                  (B[p⁺]T ,-) = ∣ ⟦ B ⟧Ty ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (I.p I.⁺))
                  (B[p⁺][q]T ,-) = ∣ ⟦ B[p⁺]T ⟧Ty ∣ I.⟨ coe (cong (I.Tm (Γ I.▹ A)) $ un) I.q ⟩
                  (f[p]t ,-) = ∣ ⟦ f ⟧Tm ∣ (I.p {A = A})
                  proof = cong T.lam∙ₑ $ refl $ refl $ refl $ refl $ refl $ (cong I.[]Tₑ $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ refl $ (cong I.[]Tₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh ∙ un) $ (cong I.⟨⟩ₑ $ refl $ refl $ un $ coh) ∙ un) $ (sym coh ∙ cong T.[]T∙ₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ (cong I.[]Tₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh ∙ un) $ refl $ (cong T.▹∙ₑ $ refl $ refl $ refl $ un $ sym coh) $ (sym coh ∙ cong T.[]T∙ₑ $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ refl $ refl $ (cong T.▹∙ₑ $ refl $ refl $ refl $ un $ sym coh) $ refl $ refl $ coh $ sym coh) $ (cong I.⟨⟩ₑ $ refl $ refl $ un $ coh) $ (cong T.⟨⟩∙ₑ $ refl $ refl $ refl $ un $ sym coh $ coh $ sym coh)) $ (cong I.appₑ $ refl $ refl $ un $ (cong I.[]Tₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh ∙ un) $ (sym coh ∙ un ∙ coh) $ coh ∙ coh) $ (sym coh ∙ cong T.app∙ₑ $ refl $ refl $ refl $ un $ sym coh $ (cong I.[]Tₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh ∙ un) $ (sym coh ∙ cong T.[]T∙ₑ $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ refl $ refl $ (cong T.▹∙ₑ $ refl $ refl $ refl $ un $ sym coh) $ refl $ refl $ coh $ sym coh) $ (sym coh ∙ un ∙ coh) $ coh $ (sym coh ∙ sym coh ∙ coh) $ sym coh) ∙ T.Πη∙
                in proof
        ; lam[]∙ = λ {n}{Γ}{A}{B}{Γ∙}{A∙}{B∙}{b}{b∙}{Δ}{Δ∙}{γ}{γ∙} →
                   let
                     (A[γ]T ,-) = ∣ ⟦ A ⟧Ty ∣ γ
                     (B[γ⁺]T ,-) = ∣ ⟦ B ⟧Ty ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺))
                     (b[γ⁺]t ,-) = ∣ ⟦ b ⟧Tm ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺))
                     proof = sym coh ∙ T.lam[]∙ ∙ cong T.lam∙ₑ $ refl $ refl $ refl $ sym un $ coh $ (sym un ∙ cong I.[]Tₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ refl $ sym coh) $ (cong T.[]T∙ₑ $ (cong I.▹ₑ $ refl $ refl $ sym un) $ refl $ refl $ refl $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ refl $ refl $ sym coh $ coh ∙ coh) $ (sym un ∙ cong I.[]tₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ refl $ refl $ refl $ sym coh) $ (cong T.[]t∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ (cong T.▹∙ₑ $ refl $ refl $ refl $ sym un $ coh) $ sym coh $ refl $ coh ∙ coh)
                   in proof
        }
