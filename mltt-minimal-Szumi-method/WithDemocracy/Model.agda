{-# OPTIONS --prop --rewriting --with-K #-}

module WithDemocracy.Model where

open import Agda.Primitive
open import Lib
import BaseModel as B

module _ {i j k}(𝕊 : B.Sorts i j k j)(ℂ : B.CwF 𝕊)(⅀ : B.Sigma 𝕊 ℂ) where
  open B.Sorts 𝕊
  open B.CwF ℂ
  open B.Sigma ⅀

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A

  record Dem : Set (i ⊔ lsuc j ⊔ k) where
    field
      K      : Con → Ty Γ
      K[]    : K Ω [ γ ]T ≈ K Ω
      un-Sub : Sub Δ Γ ≈ Tm Δ (K Γ)
      un-∘   : γ ∘ δ ~[ un-Sub ∙ cong (Tm _) $ sym K[] ] coe un-Sub γ [ δ ]t
      un-◇   : K {Γ = Γ} ◇ ≈ ⊤
      un-▹   : K {Γ = Γ} (Ω ▹ A) ≈ Σ (K Ω) (A [ coe (cong (Tm _) $ K[] ∙ sym un-Sub) q ]T)
      un-,   : γ ⁺ ∘ ⟨ a ⟩ ~[ un-Sub ∙ cong (Tm _) $ un-▹ ]
        (coe un-Sub γ , coe (cong (Tm _) $ (cong (A [_]T) $ ((coh ∙ sym q[⟨⟩] ∙ cong ([]tₑ _ _) $ K[] $ (coh ∙ coh) $ refl) ∙ sym un-∘) ∙ [∘]T)) a)

record Model {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    basemodel : B.BaseModel {i} {j} {k}
    dem : Dem (B.sorts basemodel) (B.cwf basemodel) (B.sigma basemodel)

  open B.BaseModel basemodel public
  open Dem dem public

open Model public
