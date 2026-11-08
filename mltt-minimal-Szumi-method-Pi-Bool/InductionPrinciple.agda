{-# OPTIONS --prop --rewriting --with-K --confluence-check --hidden-argument-puns #-}

open import Syntax
open import DepModel I

module InductionPrinciple {i} {j} {k} (D : DepModel {i} {j} {k}) where

open import Lib

open I

open DepModel D

private variable
  n m : ℕ
  Γ Δ Γ' Δ' Θ Ξ Ω : Con
  γ δ θ ξ : Sub Δ Γ
  A B C : Ty Γ n
  a b c d f : Tm Γ A

  Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
  γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
  A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ n A
  a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

postulate
  ⟦_⟧Con : (Γ : Con) → Con∙ Γ
  ⟦_⟧Sub : (γ : Sub Δ Γ) → Sub∙ ⟦ Δ ⟧Con ⟦ Γ ⟧Con γ
  ⟦_⟧Ty  : {n : ℕ}(A : Ty Γ n) → Ty∙ ⟦ Γ ⟧Con n A
  ⟦_⟧Tm  : (a : Tm Γ A) → Tm∙ ⟦ Γ ⟧Con ⟦ A ⟧Ty a

⟦⟧Subₑ = λ Δ Γ γ → ⟦_⟧Sub {Δ} {Γ} γ
⟦⟧Tyₑ = λ Γ n A → ⟦_⟧Ty {Γ} {n} A
⟦⟧Tmₑ = λ Γ n A a → ⟦_⟧Tm {Γ} {n} {A} a

postulate
------------------------- CwF -------------------------
  ⟦◇⟧ : ⟦ ◇ ⟧Con     ↝ ◇∙
  ⟦▹⟧ : ⟦ Γ ▹ A ⟧Con ↝ ⟦ Γ ⟧Con ▹∙ ⟦ A ⟧Ty

  {-# REWRITE ⟦◇⟧ ⟦▹⟧ #-}

  ⟦∘⟧   : ⟦ γ ∘ δ ⟧Sub ↝ ⟦ γ ⟧Sub ∘∙ ⟦ δ ⟧Sub
  ⟦id⟧  : ⟦ id {Γ = Γ} ⟧Sub ↝ id∙ {Γ∙ = ⟦ Γ ⟧Con}
  ⟦ε⟧   : ⟦ ε {Γ = Γ} ⟧Sub ↝ ε∙ {Γ∙ = ⟦ Γ ⟧Con}

  ⟦[]T⟧ : ⟦ A [ γ ]T ⟧Ty ↝ ⟦ A ⟧Ty [ ⟦ γ ⟧Sub ]T∙

  {-# REWRITE ⟦∘⟧ ⟦id⟧ ⟦ε⟧ ⟦[]T⟧ #-}

  ⟦[]t⟧ : ⟦ a [ γ ]t ⟧Tm ↝ ⟦ a ⟧Tm [ ⟦ γ ⟧Sub ]t∙
  ⟦p⟧   : ⟦ p {Γ = Γ} {A = A} ⟧Sub ↝ p∙

  {-# REWRITE ⟦[]t⟧ ⟦p⟧ #-}

  ⟦q⟧   : ⟦ q {Γ = Γ} {A = A} ⟧Tm ↝ q∙
  ⟦⁺⟧   : ⟦ _⁺ {Γ = Γ} {A = A} γ ⟧Sub ↝ ⟦ γ ⟧Sub ⁺∙
  ⟦⟨⟩⟧  : ⟦ ⟨ a ⟩ ⟧Sub ↝ ⟨ ⟦ a ⟧Tm ⟩∙
    
  {-# REWRITE ⟦q⟧ ⟦⁺⟧ ⟦⟨⟩⟧ #-}

------------------------ Lift -------------------------
  ⟦Lift⟧   : ⟦ Lift {Γ = Γ} {n = n} A ⟧Ty ↝ Lift∙ ⟦ A ⟧Ty

  {-# REWRITE ⟦Lift⟧ #-}
    
  ⟦lift⟧   : ⟦ lift {Γ = Γ} {A = A} a ⟧Tm ↝ lift∙ ⟦ a ⟧Tm
  ⟦unlift⟧ : ⟦ unlift {Γ = Γ} {A = A} a ⟧Tm ↝ unlift∙ ⟦ a ⟧Tm

  {-# REWRITE ⟦lift⟧ ⟦unlift⟧ #-}

-------------------------- U --------------------------
  ⟦U⟧  : ⟦ U {Γ = Γ} n ⟧Ty ↝ U∙ n
    
  {-# REWRITE ⟦U⟧ #-}
   
  ⟦El⟧ : ⟦ El a ⟧Ty ↝ El∙ ⟦ a ⟧Tm
  ⟦cd⟧ : ⟦ cd A ⟧Tm ↝ cd∙ ⟦ A ⟧Ty

  {-# REWRITE ⟦El⟧ ⟦cd⟧ #-}

-------------------------- Π --------------------------
  ⟦Π⟧ : ⟦ Π A B ⟧Ty ↝ Π∙ ⟦ A ⟧Ty ⟦ B ⟧Ty
    
  {-# REWRITE ⟦Π⟧ #-}

  ⟦lam⟧ : ⟦ lam b ⟧Tm ↝ lam∙ ⟦ b ⟧Tm
  ⟦app⟧ : ⟦ app f a ⟧Tm ↝ app∙ ⟦ f ⟧Tm ⟦ a ⟧Tm

  {-# REWRITE ⟦lam⟧ ⟦app⟧ #-}

------------------------ Bool -------------------------
  ⟦Bool⟧ : ⟦ Bool {Γ = Γ} ⟧Ty ↝ Bool∙
    
  {-# REWRITE ⟦Bool⟧ #-}

  ⟦true⟧ : ⟦ true {Γ = Γ} ⟧Tm ↝ true∙
  ⟦false⟧ : ⟦ false {Γ = Γ} ⟧Tm ↝ false∙

  {-# REWRITE ⟦true⟧ ⟦false⟧ #-}
    
  ⟦elim⟧ : ⟦ elim {Γ = Γ} A a b c ⟧Tm ↝ elim∙ ⟦ A ⟧Ty ⟦ a ⟧Tm ⟦ b ⟧Tm ⟦ c ⟧Tm

  {-# REWRITE ⟦elim⟧ #-}

  -- Without democracy, Ty, Sub, Tm can be injective
  Ty-inj₁ : Ty Γ n ≈ Ty Δ m → Γ ≈ Δ
  Ty-inj₂ : Ty Γ n ≈ Ty Δ m → n ≈ m

  Sub-inj₁ : Sub Δ Γ ≈ Sub Δ' Γ' → Δ ≈ Δ'
  Sub-inj₂ : Sub Δ Γ ≈ Sub Δ' Γ' → Γ ≈ Γ'

  Tm-inj₁ : Tm Γ A ≈ Tm Γ' B → Γ ≈ Γ'
  Tm-inj₂ : Tm Γ {n} A ≈ Tm Γ' {m} B → n ≈ m
  Tm-inj₃ : (e : Tm Γ {n} A ≈ Tm Γ' {m} B) → A ~[ cong Ty $ Tm-inj₁ e $ Tm-inj₂ e ] B

  -- Rules with coe
  ⟦Ty-coe⟧  : {e : Ty Γ n ≈ Ty Δ m} → ⟦ coe e A ⟧Ty ↝ coe (cong Ty∙ₑ $ Ty-inj₁ e $ (cong ⟦_⟧Con $ Ty-inj₁ e) $ Ty-inj₂ e $ coh) ⟦ A ⟧Ty
  ⟦Sub-coe⟧ : {e : Sub Δ Γ ≈ Sub Δ' Γ'}
            → let e1 = Sub-inj₁ e
                  e2 = Sub-inj₂ e
              in ⟦ coe e γ ⟧Sub ↝ coe (cong Sub∙ₑ $ e1 $ e2 $ (cong ⟦_⟧Con $ e1) $ (cong ⟦_⟧Con $ e2) $ coh) ⟦ γ ⟧Sub

  {-# REWRITE ⟦Ty-coe⟧ ⟦Sub-coe⟧ #-}

  ⟦Tm-coe⟧  : {e : Tm Γ {n} A ≈ Tm Δ {m} B}
            → let e1 = Tm-inj₁ e
                  e2 = Tm-inj₂ e
                  e3 = Tm-inj₃ e
              in ⟦ coe e a ⟧Tm ↝ coe (cong Tm∙ₑ $ e1 $ e2 $ e3 $ (cong ⟦_⟧Con $ e1) $ (cong ⟦⟧Tyₑ $ e1 $ e2 $ e3) $ coh) ⟦ a ⟧Tm

  {-# REWRITE ⟦Tm-coe⟧ #-}
