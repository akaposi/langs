{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel

module StricterSyntax.D.Bool {i} {j} {k} (T : DepModel Iₛ {i} {j} {k}) where

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

IBool∙ : BoolT∙ I ISorts∙ ICwF∙
IBool∙ = record
          { Bool∙ = T.Bool∙
          ; Bool[]∙ = sym coh ∙ T.Bool[]∙
          ; true∙ = T.true∙
          ; false∙ = T.false∙
          ; true[]∙ = sym coh ∙ T.true[]∙
          ; false[]∙ = sym coh ∙ T.false[]∙
          ; elim∙ = λ {n}{Γ}{A}{a}{b}{c}{Γ∙} A∙ a∙ b∙ c∙ →
                    let
                      (A[true]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.⟨ I.true ⟩
                      (A[false]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.⟨ I.false ⟩
                      (A[c]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.⟨ c ⟩
                      term = coe (cong T.Tm∙ₑ $ refl $ refl $ sym un $ refl $ coh $ (sym coh ∙ cong I.elimₑ $ refl $ refl $ refl $ (sym coh ∙ sym coh) $ (sym coh ∙ sym coh) $ refl)) (T.elim∙ {a = coe (cong (I.Tm Γ) $ un) a} {b = coe (cong (I.Tm Γ) $ un) b} A∙ (coe (cong T.Tm∙ₑ $ refl $ refl $ un $ refl $ sym coh $ coh) a∙) (coe (cong T.Tm∙ₑ $ refl $ refl $ un $ refl $ sym coh $ coh) b∙) c∙)
                    in term
          ; elim[]∙ = λ {n}{Γ}{Δ}{A}{a}{b}{c}{γ}{Γ∙}{Δ∙}{A∙}{a∙}{b∙}{c∙}{γ∙} →
                      let
                        (Bool[γ]T ,-) = ∣ ⟦ I.Bool ⟧Ty ∣ γ
                        (A[c]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.⟨ c ⟩
                        (A[true]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.⟨ I.true ⟩
                        (A[false]T ,-) = ∣ ⟦ A ⟧Ty ∣ I.⟨ I.false ⟩
                        (A[γ⁺]T ,-) = ∣ ⟦ A ⟧Ty ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ refl) $ refl) (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺)))
                        (a[γ]t ,-) = ∣ ⟦ a ⟧Tm ∣ γ
                        (coe-a[γ]t ,-) = ∣ coe (cong D.Tm∙ₑ
                                                  $ Tm-inj₁ (cong (I.Tm Γ {n}) $ un)
                                                  $ Tm-inj₂ (cong (I.Tm Γ {n}) $ un)
                                                  $ Tm-inj₃ (cong (I.Tm Γ {n}) $ un)
                                                  $ (cong ⟦_⟧Con $ Tm-inj₁ (cong (I.Tm Γ {n}) $ un))
                                                  $ (cong ⟦⟧Tyₑ
                                                      $ Tm-inj₁ (cong (I.Tm Γ {n}) $ un)
                                                      $ Tm-inj₂ (cong (I.Tm Γ {n}) $ un)
                                                      $ Tm-inj₃ (cong (I.Tm Γ {n}) $ un))
                                                  $ coh) ⟦ a ⟧Tm ∣ γ
                        (b[γ]t ,-) = ∣ ⟦ b ⟧Tm ∣ γ
                        (coe-b[γ]t ,-) = ∣ coe (cong D.Tm∙ₑ
                                                  $ Tm-inj₁ (cong (I.Tm Γ {n}) $ un)
                                                  $ Tm-inj₂ (cong (I.Tm Γ {n}) $ un)
                                                  $ Tm-inj₃ (cong (I.Tm Γ {n}) $ un)
                                                  $ (cong ⟦_⟧Con $ Tm-inj₁ (cong (I.Tm Γ {n}) $ un))
                                                  $ (cong ⟦⟧Tyₑ
                                                       $ Tm-inj₁ (cong (I.Tm Γ {n}) $ un)
                                                       $ Tm-inj₂ (cong (I.Tm Γ {n}) $ un)
                                                       $ Tm-inj₃ (cong (I.Tm Γ {n}) $ un))
                                                  $ coh) ⟦ b ⟧Tm ∣ γ
                        (c[γ]t ,-) = ∣ ⟦ c ⟧Tm ∣ γ
                        proof = sym coh
                              ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ un $ sym coh $ (cong I.elimₑ $ refl $ refl $ refl $ (coh ∙ coh) $ (coh ∙ coh) $ refl ∙ coh) $ refl $ refl $ refl $ sym coh $ refl
                              ∙ T.elim[]∙ {a = coe (cong (I.Tm Γ {n}) $ un) a} {b = coe (cong (I.Tm Γ {n}) $ un) b} {a∙ = coe (cong T.Tm∙ₑ $ refl $ refl $ un $ refl $ sym coh $ coh) a∙} {b∙ = coe (cong T.Tm∙ₑ $ refl $ refl $ un $ refl $ sym coh $ coh) b∙}
                              ∙ cong T.elim∙ₑ
                                  $ refl
                                  $ refl
                                  $ (sym un ∙ cong I.[]Tₑ $ refl $ refl $ refl $ refl $ (sym coh ∙ sym coh ∙ coh))
                                  $ (sym coh ∙ sym un ∙ cong I.[]tₑ $ refl $ refl $ refl $ sym un $ sym coh $ refl ∙ coh ∙ coh)
                                  $ (sym coh ∙ sym un ∙ cong I.[]tₑ $ refl $ refl $ refl $ sym un $ sym coh $ refl ∙ coh ∙ coh)
                                  $ (sym coh ∙ sym un ∙ coh)
                                  $ refl
                                  $ (cong T.[]T∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ (sym coh ∙ sym coh ∙ coh) $ (sym coh ∙ coh ∙ coh) ∙ coh)
                                  $ (sym coh ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ sym un $ coh $ sym coh $ refl $ refl $ refl $ sym coh $ refl ∙ coh ∙ coh ∙ coh)
                                  $ (sym coh ∙ cong T.[]t∙ₑ $ refl $ refl $ refl $ sym un $ coh $ sym coh $ refl $ refl $ refl $ sym coh $ refl ∙ coh ∙ coh ∙ coh)
                                  $ (sym coh ∙ coh ∙ coh)
                              ∙ coh
                      in proof
          ; Boolβ₁∙ = sym coh ∙ T.Boolβ₁∙ ∙ sym coh
          ; Boolβ₂∙ = sym coh ∙ T.Boolβ₂∙ ∙ sym coh
          }
