{-# OPTIONS --prop --rewriting --with-K #-}

module DepModel where

open import Lib
open import Syntax
import Model as M

module I = M.Model I
open I

record Sorts∙ i j k l : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  field
    Con∙ : Con → Set i
    Sub∙ : {Δ Γ : Con}(Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → Set j
    Ty∙  : {Γ : Con}(Γ∙ : Con∙ Γ)(A : Ty Γ) → Set k
    Tm∙  : {Γ : Con}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A)(t : Tm Γ A) → Set l

  Sub∙ₑ = λ Δ Γ → Sub∙ {Δ} {Γ}
  Ty∙ₑ = λ Γ → Ty∙ {Γ}
  Tm∙ₑ = λ Γ A → Tm∙ {Γ} {A}

module _ {i j k l}(𝕊 : Sorts∙ i j k l) where
  open Sorts∙ 𝕊

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record CwF∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 8 _∘∙_
    infixl 5 _▹∙_
    infixl 9 _[_]T∙ _[_]t∙
    infixl 10 _⁺∙
    infixl 11 ⟨_⟩∙
    field
      _∘∙_    : (γ∙ : Sub∙ Δ∙ Γ∙ γ)(δ∙ : Sub∙ Θ∙ Δ∙ δ) → Sub∙ Θ∙ Γ∙ (γ ∘ δ)
      ass∙    : (γ∙ ∘∙ δ∙) ∘∙ θ∙ ~[ cong (Sub∙ _ _) $ ass ] γ∙ ∘∙ (δ∙ ∘∙ θ∙)
      id∙     : Sub∙ Γ∙ Γ∙ id
      idl∙    : id∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ idl ] γ∙
      idr∙    : γ∙ ∘∙ id∙ ~[ cong (Sub∙ _ _) $ idr ] γ∙
      ◇∙      : Con∙ ◇
      ε∙      : Sub∙ Γ∙ ◇∙ ε
      ◇η∙     : γ∙ ≈ ε∙
      _[_]T∙  : (A∙ : Ty∙ Γ∙ A)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Ty∙ Δ∙ (A [ γ ]T)

    []T∙ₑ = λ Δ Γ A Δ∙ Γ∙ A∙ γ γ∙ → _[_]T∙ {Γ} {Γ∙} {A} {Δ} {Δ∙} {γ} A∙ γ∙

    field
      [∘]T∙   : A∙ [ γ∙ ∘∙ δ∙ ]T∙ ~[ cong (Ty∙ _) $ [∘]T ] A∙ [ γ∙ ]T∙ [ δ∙ ]T∙
      [id]T∙  : A∙ [ id∙ ]T∙ ~[ cong (Ty∙ _) $ [id]T ] A∙
      _[_]t∙  : (a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
      [∘]t∙   : a∙ [ γ∙ ∘∙ δ∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Θ∙) $ [∘]T $ [∘]T∙ $ [∘]t ] a∙ [ γ∙ ]t∙ [ δ∙ ]t∙
      [id]t∙  : a∙ [ id∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Θ∙) $ [id]T $ [id]T∙ $ [id]t ] a∙
      _▹∙_    : (Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A) → Con∙ (Γ ▹ A)
      p∙      : Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
      q∙      : Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ ]T∙) q
      _⁺∙     : (γ∙ : Sub∙ Δ∙ Γ∙ γ) → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) (Γ∙ ▹∙ A∙) (γ ⁺)
      ∘⁺∙     : (γ∙ ∘∙ δ∙) ⁺∙ ~[ cong Sub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Θ∙) $ [∘]T $ [∘]T∙) $ cong (Γ∙ ▹∙ A∙) $ ∘⁺ ] γ∙ ⁺∙ ∘∙ δ∙ ⁺∙
      id⁺∙    : id∙ ⁺∙ ~[ cong Sub∙ₑ $ (cong (Γ ▹_) $ [id]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Γ∙) $ [id]T $ [id]T∙) $ cong (Γ∙ ▹∙ A∙) $ id⁺ ] id∙
      ⟨_⟩∙    : (a∙ : Tm∙ Γ∙ A∙ a) → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ a ⟩
      ⟨⟩∘∙    : ⟨ a∙ ⟩∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ ⟨⟩∘ ] γ∙ ⁺∙ ∘∙ ⟨ a∙ [ γ∙ ]t∙ ⟩∙
      p∘⁺∙    : p∙ ∘∙ γ∙ ⁺∙ ~[ cong (Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) _) $ p∘⁺ ] γ∙ ∘∙ p∙
      p∘⟨⟩∙   : p∙ ∘∙ ⟨ a∙ ⟩∙ ~[ cong (Sub∙ _ _) $ p∘⟨⟩ ] id∙

    [p][⁺]T∙ : A∙ [ p∙ ]T∙ [ γ∙ ⁺∙ ]T∙ ~[ cong (Ty∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙)) $ [p][⁺]T ] A∙ [ γ∙ ]T∙ [ p∙ ]T∙
    [p][⁺]T∙ {A∙ = A∙} = sym [∘]T∙ ∙ {!!}
    
    field
      q[⁺]∙   : q∙ [ γ∙ ⁺∙ ]t∙ ~[ cong Tm∙ₑ $ cong (Δ ▹ A [ γ ]T) $ [p][⁺]T $ cong (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) $ {!!} $ {!!} ] q∙
      q[⟨⟩]∙  : q∙ [ ⟨ a∙ ⟩∙ ]t∙ ~[ {!!} ] a∙
      ▹η∙     : id∙ {Γ∙ = Γ∙ ▹∙ A∙} ~[ cong (Sub∙ _ _) $ ▹η ] p∙ ⁺∙ ∘∙ ⟨ q∙ ⟩∙
    []t∙ : (A∙ : Ty∙ Γ∙ A)(a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
    []t∙ = λ A∙ a∙ γ∙ → _[_]t∙ {A∙ = A∙} a∙ γ∙
{-
    [p][⁺]T : A [ p ]T [ γ ⁺ ]T ~[ cong (Ty (Δ ▹ A [ γ ]T)) ] A [ γ ]T [ p ]T
    [p][⁺]T {A = A} = sym [∘]T ∙ cong (A [_]T) $ p∘⁺ ∙ [∘]T
    
    [p][⟨⟩]T : A [ p ]T [ ⟨ a ⟩ ]T ≈ A
    [p][⟨⟩]T {A = A} = sym [∘]T ∙ cong (A [_]T) $ p∘⟨⟩ ∙ [id]T

    [▹η]T : A ≈ A [ p ⁺ ]T [ ⟨ q ⟩ ]T
    [▹η]T {A = A} = sym [id]T ∙ cong (A [_]T) $ ▹η ∙ [∘]T

    [⟨⟩][]T : A [ ⟨ a ⟩ ]T [ γ ]T ≈ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
    [⟨⟩][]T {A = A} = sym [∘]T ∙ cong (A [_]T) $ ⟨⟩∘ ∙ [∘]T
-}

    [p][⟨⟩]T∙ : A∙ [ p∙ ]T∙ [ ⟨ a∙ ⟩∙ ]T∙ ~[ cong (Ty∙ _) $ [p][⟨⟩]T ] A∙
    [p][⟨⟩]T∙ {A∙ = A∙} = {!sym [∘]T∙ !}

    [▹η]T∙ : A∙ ~[ cong (Ty∙ _) $ [▹η]T ] A∙ [ p∙ ⁺∙ ]T∙ [ ⟨ q∙ ⟩∙ ]T∙
    [▹η]T∙ {A∙ = A∙} = {!!}

    [⟨⟩][]T∙ : A∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ [⟨⟩][]T ] A∙ [ γ∙ ⁺∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙
    [⟨⟩][]T∙ {A∙ = A∙} = {!!}
