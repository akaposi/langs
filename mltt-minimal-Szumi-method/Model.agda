{-# OPTIONS --prop --rewriting --with-K #-}

module Model where

open import Prelude

record Sorts i j k l : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where field
  Con : Set i
  Sub : Con → Con → Set j
  Ty  : Con → Set k
  Tm  : (Γ : Con) → Ty Γ → Set l

module _ {i j k l}(𝕊 : Sorts i j k l) where
  open Sorts 𝕊

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A

  record CwF : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 9 _∘_
    infixl 2 _▹_
    infixl 9 _[_]T _[_]t
    infixl 10 _⁺
    field
      _∘_    : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      ass    : (γ ∘ δ) ∘ θ ≈ γ ∘ (δ ∘ θ)
      id     : Sub Γ Γ
      idl    : id ∘ γ ≈ γ
      idr    : γ ∘ id ≈ γ
      ◇      : Con
      ε      : Sub Γ ◇
      ◇η     : γ ≈ ε
      _[_]T  : Ty Γ → Sub Δ Γ → Ty Δ
      [∘]T   : A [ γ ∘ δ ]T ≈ A [ γ ]T [ δ ]T
      [id]T  : A [ id ]T ≈ A
      _[_]t  : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
      [∘]t   : a [ γ ∘ δ ]t ~[ ap (Tm Θ) $ [∘]T ] a [ γ ]t [ δ ]t
      [id]t  : a [ id ]t ~[ ap (Tm Γ) $ [id]T ] a
      _▹_    : (Γ : Con) → Ty Γ → Con
      p      : Sub (Γ ▹ A) Γ
      q      : Tm  (Γ ▹ A) (A [ p ]T)
      _⁺     : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
      ∘-⁺    : (γ ∘ δ) ⁺ ~[ ap Sub $ (ap (Θ ▹_) $ [∘]T {A = A}) $ refl ] γ ⁺ ∘ δ ⁺
      id-⁺   : id ⁺ ~[ ap Sub $ (ap (Γ ▹_) $ [id]T {A = A}) $ refl ] id
      ⟨_⟩    : Tm Γ A → Sub Γ (Γ ▹ A)
      ⟨⟩-∘   : ⟨ a ⟩ ∘ γ ≈ γ ⁺ ∘ ⟨ a [ γ ]t ⟩
      p-⁺    : p {A = A} ∘ γ ⁺ ≈ γ ∘ p
      p-⟨⟩   : p ∘ ⟨ a ⟩ ≈ id
      q-⁺    : q [ γ ⁺ ]t ~[ ap (Tm _) $ (sym [∘]T ∙ ap (A [_]T) $ p-⁺ ∙ [∘]T) ] q
      q-⟨⟩   : q [ ⟨ a ⟩ ]t ~[ ap (Tm _) $ (sym [∘]T ∙ ap (A [_]T) $ p-⟨⟩ ∙ [id]T) ] a
      ▹η     : id {Γ ▹ A} ≈ p ⁺ ∘ ⟨ q ⟩
    []tₑ : (A : Ty Γ) → Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
    []tₑ = λ A a γ → _[_]t {A = A} a γ

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A

  record Sigma : Set (i ⊔ j ⊔ k ⊔ l) where
    infixr 4 _,_
    field
      ⊤   : Ty Γ
      ⊤[] : ⊤ [ γ ]T ≈ ⊤
      tt  : Tm Γ ⊤
      ⊤η  : a ≈ tt
      Σ   : (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
      Σ[] : Σ A B [ γ ]T ≈ Σ (A [ γ ]T) (B [ γ ⁺ ]T)
      _,_ : (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T) → Tm Γ (Σ A B)
      ,[] : (a , b) [ γ ]t ~[ ap (Tm _) $ Σ[] ] (a [ γ ]t , coe (ap (Tm _) $ (sym [∘]T ∙ ap (B [_]T) $ ⟨⟩-∘ ∙ [∘]T)) (b [ γ ]t))
      fst : Tm Γ (Σ A B) → Tm Γ A
      snd : (w : Tm Γ (Σ A B)) → Tm Γ (B [ ⟨ fst w ⟩ ]T)
      Σβ₁ : fst (a , b) ≈ a
      Σβ₂ : snd (a , b) ~[ ap (Tm _) $ (ap (B [_]T) $ (ap ⟨_⟩ $ Σβ₁)) ] b
      Ση  : {w : Tm Γ (Σ A B)} → w ≈ (fst w , snd w)

    -- TODO: derive tt[], fst[], snd[]

module _ {i j k}(𝕊 : Sorts i j k j)(ℂ : CwF 𝕊)(𝔻 : Sigma 𝕊 ℂ) where
  open Sorts 𝕊
  open CwF ℂ
  open Sigma 𝔻

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A

  record Dem : Set (i ⊔ lsuc j ⊔ k) where field
      K      : Con → Ty Γ
      K[]    : K Ω [ γ ]T ≈ K Ω
      un-Sub : Sub Δ Γ ≈ Tm Δ (K Γ)
      un-∘   : γ ∘ δ ~[ un-Sub ∙ ap (Tm _) $ sym K[] ] coe un-Sub γ [ δ ]t
      un-◇   : K {Γ = Γ} ◇ ≈ ⊤
      un-▹   : K {Γ = Γ} (Ω ▹ A) ≈ Σ (K Ω) (A [ coe (ap (Tm _) $ K[] ∙ sym un-Sub) q ]T)
      un-,   : γ ⁺ ∘ ⟨ a ⟩ ~[ un-Sub ∙ ap (Tm _) $ un-▹ ]
        (coe un-Sub γ , coe (ap (Tm _) $ (ap (A [_]T) $ ((sym coh ∙ sym q-⟨⟩ ∙ ap []tₑ $ K[] $ (sym coh ∙ sym coh) $ refl) ∙ sym un-∘) ∙ [∘]T)) a)
