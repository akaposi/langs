{-# OPTIONS --prop --rewriting --with-K --confluence-check --hidden-argument-puns #-}

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
    Ty∙  : {Γ : Con}(Γ∙ : Con∙ Γ)(n : ℕ)(A : Ty Γ n) → Set k
    Tm∙  : {Γ : Con}{n : ℕ}{A : Ty Γ n}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ n A)(t : Tm Γ A) → Set l

  Sub∙ₑ = λ Δ Γ Δ∙ Γ∙ γ → Sub∙ {Δ} {Γ} Δ∙ Γ∙ γ
  Ty∙ₑ = λ Γ Γ∙ n A → Ty∙ {Γ} Γ∙ n A
  Tm∙ₑ = λ Γ n A Γ∙ A∙ a → Tm∙ {Γ} {n} {A} Γ∙ A∙ a

module _ {i j k l}(𝕊 : Sorts∙ i j k l) where
  open Sorts∙ 𝕊

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ n A
    a∙ b∙ c∙ : Tm∙ {Γ = Γ} {n = n} {A = A} Γ∙ A∙ a

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
      ◇η∙     : {γ∙ : Sub∙ Γ∙ ◇∙ γ} → γ∙ ~[ cong (Sub∙ _ _) $ ◇η ] ε∙
      _[_]T∙  : (A∙ : Ty∙ Γ∙ n A)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Ty∙ Δ∙ n (A [ γ ]T)

    []T∙ₑ = λ Δ Γ n A Δ∙ Γ∙ A∙ γ γ∙ → _[_]T∙ {Γ} {Γ∙} {n} {A} {Δ} {Δ∙} {γ} A∙ γ∙

    field
      [∘]T∙   : A∙ [ γ∙ ∘∙ δ∙ ]T∙ ~[ cong (Ty∙ _ _) $ [∘]T ] A∙ [ γ∙ ]T∙ [ δ∙ ]T∙
      [id]T∙  : A∙ [ id∙ ]T∙ ~[ cong (Ty∙ _ _) $ [id]T ] A∙
      _[_]t∙  : (a∙ : Tm∙ Γ∙ A∙ a)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) (a [ γ ]t)
      [∘]t∙   : a∙ [ γ∙ ∘∙ δ∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Θ∙) $ [∘]T $ [∘]T∙ $ [∘]t ] a∙ [ γ∙ ]t∙ [ δ∙ ]t∙
      [id]t∙  : a∙ [ id∙ ]t∙ ~[ cong (λ x → Tm∙ {A = x} Θ∙) $ [id]T $ [id]T∙ $ [id]t ] a∙
      _▹∙_    : (Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ n A) → Con∙ (Γ ▹ A)
      p∙      : Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
      q∙      : Tm∙ (Γ∙ ▹∙ A∙) (A∙ [ p∙ ]T∙) q
      _⁺∙     : (γ∙ : Sub∙ Δ∙ Γ∙ γ) → Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) (Γ∙ ▹∙ A∙) (γ ⁺)
      ∘⁺∙     : (γ∙ ∘∙ δ∙) ⁺∙ ~[ cong Sub∙ₑ $ (cong (Θ ▹_) $ [∘]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Θ∙) $ [∘]T $ [∘]T∙) $ cong (Γ∙ ▹∙ A∙) $ ∘⁺ ] γ∙ ⁺∙ ∘∙ δ∙ ⁺∙
      id⁺∙    : id∙ ⁺∙ ~[ cong Sub∙ₑ $ (cong (Γ ▹_) $ [id]T) $ cong (Γ ▹ A) $ (cong (λ x → _▹∙_ {A = x} Γ∙) $ [id]T $ [id]T∙) $ cong (Γ∙ ▹∙ A∙) $ id⁺ ] id∙
      ⟨_⟩∙    : (a∙ : Tm∙ Γ∙ A∙ a) → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ a ⟩
      ⟨⟩∘∙    : ⟨ a∙ ⟩∙ ∘∙ γ∙ ~[ cong (Sub∙ _ _) $ ⟨⟩∘ ] γ∙ ⁺∙ ∘∙ ⟨ a∙ [ γ∙ ]t∙ ⟩∙
      p∘⁺∙    : p∙ ∘∙ γ∙ ⁺∙ ~[ cong (Sub∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) _) $ p∘⁺ ] γ∙ ∘∙ p∙
      p∘⟨⟩∙   : p∙ ∘∙ ⟨ a∙ ⟩∙ ~[ cong (Sub∙ _ _) $ p∘⟨⟩ ] id∙

    []t∙ₑ = λ Γ Γ∙ n A A∙ a Δ Δ∙ γ a∙ γ∙ → _[_]t∙ {Γ} {Γ∙} {n} {A} {A∙} {a} {Δ} {Δ∙} {γ} a∙ γ∙

    ⟨⟩∙ₑ = λ Γ Γ∙ n A A∙ a a∙ → ⟨_⟩∙ {Γ} {Γ∙} {n} {A} {A∙} {a} a∙

    ∘∙ₑ = λ Γ Γ∙ Δ Δ∙ Θ Θ∙ γ δ γ∙ δ∙ → _∘∙_ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {Θ} {Θ∙} {δ} γ∙ δ∙

    ⁺∙ₑ = λ Γ Γ∙ Δ Δ∙ n A A∙ γ γ∙  → _⁺∙ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {n} {A} {A∙} γ∙

    ▹∙ₑ = λ Γ Γ∙ n A A∙ → _▹∙_ {Γ} {n} {A} Γ∙ A∙

    p∙ₑ = λ Γ Γ∙ n A A∙ → p∙ {Γ} {Γ∙} {n} {A} {A∙}

    q∙ₑ = λ Γ Γ∙ n A A∙ → q∙ {Γ} {Γ∙} {n} {A} {A∙}

    weave∙ : {A : Ty Γ n}{γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ}
             {A∙ : Ty∙ Γ∙ n A}{γ∙ : Sub∙ Ξ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Ξ∙ δ}{γ'∙ : Sub∙ Δ∙ Γ∙ γ'}{δ'∙ : Sub∙ Θ∙ Δ∙ δ'}
             (e : γ ∘ δ ≈ γ' ∘ δ')(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] γ'∙ ∘∙ δ'∙)
           → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _ _) $ weave e ] A∙ [ γ'∙ ]T∙ [ δ'∙ ]T∙
    weave∙ e e∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _ _) $ e $ e∙ ∙ [∘]T∙

    annihilate∙ : (e : γ ∘ δ ≈ id)(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] id∙ {Γ∙ = Γ∙})
                → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _ _) $ annihilate e ] A∙
    annihilate∙ e e∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _ _) $ e $ e∙ ∙ [id]T∙

    weave-t∙ : {A : Ty Γ n}{a : Tm Γ A}{γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ}
               {A∙ : Ty∙ Γ∙ n A}{a∙ : Tm∙ Γ∙ A∙ a}{γ∙ : Sub∙ Ξ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Ξ∙ δ}{γ'∙ : Sub∙ Δ∙ Γ∙ γ'}{δ'∙ : Sub∙ Θ∙ Δ∙ δ'}
               (e : γ ∘ δ ≈ γ' ∘ δ')(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] γ'∙ ∘∙ δ'∙)
             → a∙ [ γ∙ ]t∙ [ δ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ weave e $ refl $ weave∙ e e∙ $ weave-t e ] a∙ [ γ'∙ ]t∙ [ δ'∙ ]t∙
    weave-t∙ e e∙ = sym [∘]t∙ ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ e $ refl $ e∙ ∙ [∘]t∙


    annihilate-t∙ : (e : γ ∘ δ ≈ id)(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] id∙ {Γ∙ = Γ∙})
                  → a∙ [ γ∙ ]t∙ [ δ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ annihilate e $ refl $ annihilate∙ e e∙ $ annihilate-t e ] a∙
    annihilate-t∙ e e∙ = sym [∘]t∙ ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ e $ refl $ e∙ ∙ [id]t∙
    
    [p][⁺]T∙ : A∙ [ p∙ ]T∙ [ γ∙ ⁺∙ ]T∙ ~[ cong (Ty∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) n) $ [p][⁺]T ] A∙ [ γ∙ ]T∙ [ p∙ ]T∙
    [p][⁺]T∙ = weave∙ p∘⁺ p∘⁺∙

    [p][⁺]t∙ : a∙ [ p∙ {A∙ = A∙} ]t∙ [ γ∙ ⁺∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ [p][⁺]T $ refl $ [p][⁺]T∙ $ [p][⁺]t ] a∙ [ γ∙ ]t∙ [ p∙ {A∙ = A∙ [ γ∙ ]T∙} ]t∙
    [p][⁺]t∙ = weave-t∙ p∘⁺ p∘⁺∙
    
    [p][⟨⟩]T∙ : A∙ [ p∙ ]T∙ [ ⟨ a∙ ⟩∙ ]T∙ ~[ cong (Ty∙ _ _) $ [p][⟨⟩]T ] A∙
    [p][⟨⟩]T∙ = annihilate∙ p∘⟨⟩ p∘⟨⟩∙

    [p][⟨⟩]t∙ : a∙ [ p∙ ]t∙ [ ⟨ b∙ ⟩∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ [p][⟨⟩]T $ refl $ [p][⟨⟩]T∙ $ [p][⟨⟩]t ] a∙
    [p][⟨⟩]t∙ = annihilate-t∙ p∘⟨⟩ p∘⟨⟩∙
    
    field
      q[⁺]∙   : q∙ [ γ∙ ⁺∙ ]t∙ ~[ cong Tm∙ₑ $ reflₑ (Δ ▹ A [ γ ]T) $ reflₑ n $ [p][⁺]T $ reflₑ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) $ [p][⁺]T∙ $ q[⁺] ] q∙
      q[⟨⟩]∙  : q∙ [ ⟨ a∙ ⟩∙ ]t∙ ~[ cong (λ x → Tm∙ₑ _ n x Γ∙) $ [p][⟨⟩]T $ [p][⟨⟩]T∙ $ q[⟨⟩] ] a∙
      ▹η∙     : id∙ {Γ∙ = Γ∙ ▹∙ A∙} ~[ cong (Sub∙ _ _) $ ▹η ] p∙ ⁺∙ ∘∙ ⟨ q∙ ⟩∙

    [▹η]T∙ : A∙ ~[ cong (Ty∙ _ n) $ [▹η]T ] A∙ [ p∙ ⁺∙ ]T∙ [ ⟨ q∙ ⟩∙ ]T∙
    [▹η]T∙ = sym (annihilate∙ (sym ▹η) (sym ▹η∙))

    [▹η]t∙ : a∙ ~[ cong Tm∙ₑ $ refl $ refl $ [▹η]T $ refl $ [▹η]T∙ $ [▹η]t ] a∙ [ p∙ ⁺∙ ]t∙ [ ⟨ q∙ ⟩∙ ]t∙
    [▹η]t∙ = sym (annihilate-t∙ (sym ▹η) (sym ▹η∙))

    [⟨⟩][]T∙ : A∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _ n) $ [⟨⟩][]T ] A∙ [ γ∙ ⁺∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙
    [⟨⟩][]T∙ = weave∙ ⟨⟩∘ ⟨⟩∘∙

    [⟨⟩][]t∙ : a∙ [ ⟨ b∙ ⟩∙ ]t∙ [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ $ [⟨⟩][]t ] a∙ [ γ∙ ⁺∙ ]t∙ [ ⟨ b∙ [ γ∙ ]t∙ ⟩∙ ]t∙
    [⟨⟩][]t∙ = weave-t∙ ⟨⟩∘ ⟨⟩∘∙

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ n A
    a∙ b∙ c∙ : Tm∙ {Γ = Γ} {n = n} {A = A} Γ∙ A∙ a

  record LiftT∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      Lift∙     : Ty∙ Γ∙ n A → Ty∙ Γ∙ (suc n) (Lift A)
      lift∙     : Tm∙ Γ∙ A∙ a → Tm∙ Γ∙ (Lift∙ A∙) (lift a)
      unlift∙   : Tm∙ Γ∙ (Lift∙ A∙) a → Tm∙ Γ∙ A∙ (unlift a)
      Liftβ∙    : unlift∙ (lift∙ a∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ Liftβ ] a∙
      Liftη∙    : lift∙ (unlift∙ a∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ Liftη ] a∙
      Lift[]∙   : (Lift∙ A∙ [ γ∙ ]T∙) ~[ cong Ty∙ₑ $ refl $ refl $ refl $ Lift[] ] Lift∙ (A∙ [ γ∙ ]T∙)
      lift[]∙   : lift∙ a∙ [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ Lift[] $ refl $ Lift[]∙ $ lift[] ] lift∙ (a∙ [ γ∙ ]t∙)

    lift∙ₑ = λ Γ Γ∙ n A A∙ a a∙ → lift∙ {Γ} {Γ∙} {n} {A} {A∙} {a} a∙
    
    unlift∙ₑ = λ Γ Γ∙ n A A∙ a a∙ → unlift∙ {Γ} {Γ∙} {n} {A} {A∙} {a} a∙

    unlift[]∙ : (unlift∙ a∙) [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ unlift[] ] unlift∙ (coe (cong Tm∙ₑ $ refl $ refl $ Lift[] $ refl $ Lift[]∙ $ coh) (a∙ [ γ∙ ]t∙))
    unlift[]∙ = sym Liftβ∙ ∙ cong unlift∙ₑ $ refl $ refl $ refl $ refl $ refl $ (sym lift[] ∙ cong _[ _ ]t $ Liftη ∙ coh) $ (sym lift[]∙ ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ Liftη $ refl $ refl $ refl $ Liftη∙ $ refl ∙ coh)

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c d f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ n A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record UT∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      U∙    : (n : ℕ) → Ty∙ Γ∙ (suc n) (U n)
      El∙   : Tm∙ Γ∙ (U∙ n) a → Ty∙ Γ∙ n (El a)
      cd∙   : Ty∙ Γ∙ n A → Tm∙ Γ∙ (U∙ n) (cd A)
      Uβ∙   : El∙ (cd∙ A∙) ~[ cong Ty∙ₑ $ refl $ refl $ refl $ Uβ ] A∙
      Uη∙   : cd∙ (El∙ a∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ Uη ] a∙
      U[]∙  : (U∙ n) [ γ∙ ]T∙ ~[ cong Ty∙ₑ $ refl $ refl $ refl $ U[] ] U∙ n
      cd[]∙ : cd∙ A∙ [ γ∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ U[] $ refl $ U[]∙ $ cd[] ] cd∙ (A∙ [ γ∙ ]T∙)

    El∙ₑ = λ Γ Γ∙ n a a∙ → El∙ {Γ} {Γ∙} {n} {a} a∙

    cd∙ₑ = λ Γ Γ∙ n A A∙ → cd∙ {Γ} {Γ∙} {n} {A} A∙

    El[]∙ : El∙ a∙ [ γ∙ ]T∙ ~[ cong Ty∙ₑ $ refl $ refl $ refl $ El[] ] El∙ (coe (cong Tm∙ₑ $ refl $ refl $ U[] $ refl $ U[]∙ $ coh) (a∙ [ γ∙ ]t∙))
    El[]∙ {γ∙} = sym Uβ∙ ∙ cong El∙ₑ $ refl $ refl $ refl $ (sym cd[] ∙ cong _[ _ ]t $ Uη ∙ coh) $ (sym cd[]∙ ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ Uη $ refl $ refl $ refl $ Uη∙ $ refl ∙ coh)

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c d f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ n A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record Pi∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 9 _[_]Π∙
    field
      Π∙     : (A∙ : Ty∙ Γ∙ n A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) n B) → Ty∙ Γ∙ n (Π A B)
      Π[]∙   : Π∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _ n) $ Π[] ] Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)

    _[_]Π∙ : (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)) (f [ γ ]Π)
    f∙ [ γ∙ ]Π∙ = coe (cong (Tm∙ₑ _ _) $ Π[] $ refl $ Π[]∙ $ []Π) (f∙ [ γ∙ ]t∙)

    []Π∙ₑ = λ Γ Γ∙ n A A∙ B B∙ Δ Δ∙ f f∙ γ γ∙ → _[_]Π∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {f} {Δ} {Δ∙} {γ} f∙ γ∙

    []Π∙   : a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _ _) $ Π[] $ refl $ Π[]∙ $ []Π ] a∙ [ γ∙ ]Π∙
    []Π∙ = coh

    Π∙ₑ = λ Γ Γ∙ n A A∙ B B∙ → Π∙ {Γ} {Γ∙} {n} {A} {B} A∙ B∙

    field
      lam∙   : (b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b) → Tm∙ Γ∙ (Π∙ A∙ B∙) (lam b)
      app∙   : (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(a∙ : Tm∙ Γ∙ A∙ a) → Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) (app f a)
      Πβ∙    : app∙ (lam∙ b∙) a∙ ~[ cong (Tm∙ _ _) $ Πβ ] b∙ [ ⟨ a∙ ⟩∙ ]t∙
      Πη∙    : lam∙ (app∙ (f∙ [ p∙ ]Π∙) q∙) ~[ cong (Tm∙ₑ _ _) $ (cong (Π _) $ sym [▹η]T) $ refl $ (cong (Π∙ₑ _ _ _ _ _) $ sym [▹η]T $ sym [▹η]T∙) $ Πη ] f∙
      lam[]∙ : lam∙ b∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _ _) $ Π[] $ refl $ Π[]∙ $ lam[] ] lam∙ (b∙ [ γ∙ ⁺∙ ]t∙)

    lam∙ₑ = λ Γ Γ∙ n A A∙ B B∙ t t∙ → lam∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {t} t∙
    
    app∙ₑ = λ Γ Γ∙ n A A∙ B B∙ f a f∙ a∙ → app∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {f} {a} f∙ a∙

    app'∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) b → Tm∙ (Γ∙ ▹∙ A∙) B∙ (app' b)
    app'∙ {A∙} b∙ = coe (cong Tm∙ₑ $ refl $ refl $ sym [▹η]T $ refl $ sym [▹η]T∙ $ coh) (app∙ (b∙ [ p∙ {A∙ = A∙} ]Π∙) q∙)

    app'∙ₑ = λ Γ Γ∙ n A A∙ B B∙ t t∙ → app'∙ {Γ} {Γ∙} {n} {A} {A∙} {B} {B∙} {t} t∙

    app'β∙ : app'∙ (lam∙ b∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'β ] b∙
    app'β∙ = sym coh ∙ cong app∙ₑ $ refl $ refl $ refl $ refl $ refl $ refl $ refl $ (sym []Π ∙ lam[]) $ refl $ (sym []Π∙ ∙ lam[]∙) $ refl ∙ Πβ∙ ∙ sym [▹η]t∙

    app'η∙ : lam∙ (app'∙ b∙) ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'η ] b∙
    app'η∙ = cong lam∙ₑ $ refl $ refl $ refl $ refl $ refl $ [▹η]T $ [▹η]T∙ $ sym coh $ sym coh ∙ Πη∙

    app'[]∙ : app'∙ b∙ [ γ∙ ⁺∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'[] ] app'∙ (b∙ [ γ∙ ]Π∙)
    app'[]∙ {(Γ)} {(n)} {(Γ∙)} {(A)} {(B)} {(b)} {(A∙)} {(B∙)} {(b∙)} {(Δ)} {(Δ∙)} {(γ)} {(γ∙)} =
            sym app'β∙
          ∙ sym coh
          ∙ cong app∙ₑ
              $ refl
              $ refl
              $ refl
              $ refl
              $ refl
              $ refl
              $ refl
              $ (cong _[ p ]Π $ (sym lam[] ∙ cong _[ γ ]t $ app'η ∙ []Π))
              $ refl
              $ (cong []Π∙ₑ
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ (sym lam[] ∙ cong _[ γ ]t $ app'η ∙ []Π)
                   $ (sym lam[]∙ ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'η $ refl $ refl $ refl $ app'η∙ $ refl ∙ []Π∙)
                   $ refl
                   $ refl)
              $ refl
          ∙ coh

    app'≈app∙ : app'∙ b∙ [ ⟨ a∙ ⟩∙ ]t∙ ~[ cong Tm∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'≈app ] app∙ b∙ a∙
    app'≈app∙ = cong []t∙ₑ
                  $ refl
                  $ refl
                  $ refl
                  $ [▹η]T
                  $ [▹η]T∙
                  $ sym coh
                  $ refl
                  $ refl
                  $ refl
                  $ sym coh
                  $ refl
              ∙ sym Πβ∙
              ∙ cong app∙ₑ
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ refl
                   $ sym [▹η]T
                   $ sym [▹η]T∙
                   $ Πη
                   $ refl
                   $ Πη∙
                   $ refl

    app[]∙ : app∙ f∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _ _) $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ $ app[] ] app∙ (f∙ [ γ∙ ]Π∙) (a∙ [ γ∙ ]t∙)
    app[]∙ = cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ sym app'≈app $ refl $ refl $ refl $ sym app'≈app∙ $ refl
           ∙ [⟨⟩][]t∙
           ∙ cong []t∙ₑ $ refl $ refl $ refl $ refl $ refl $ app'[] $ refl $ refl $ refl $ app'[]∙ $ refl
           ∙ app'≈app∙

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c d f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ n A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record BoolT∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      Bool∙    : Ty∙ Γ∙ 0 Bool
      Bool[]∙  : Bool∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _ _) $ Bool[] ] Bool∙
      true∙    : Tm∙ Γ∙ Bool∙ true
      false∙   : Tm∙ Γ∙ Bool∙ false
      true[]∙  : true∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _ _) $ Bool[] $ refl $ Bool[]∙ $ true[] ] true∙
      false[]∙ : false∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _ _) $ Bool[] $ refl $ Bool[]∙ $ false[] ] false∙
      elim∙    : {Γ : Con} {A : Ty (Γ ▹ Bool) n}
                 {a : Tm Γ (A [ ⟨ true ⟩ ]T)}
                 {b : Tm Γ (A [ ⟨ false ⟩ ]T)}
                 {c : Tm Γ Bool}
                 {Γ∙ : Con∙ Γ}
                 (A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) n A)
                 (a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a)
                 (b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b)
                 (c∙ : Tm∙ Γ∙ Bool∙ c)
               → Tm∙ Γ∙ (A∙ [ ⟨ c∙ ⟩∙ ]T∙) (elim A a b c)
      elim[]∙  :
        {Γ Δ : Con}
        {A : Ty (Γ ▹ Bool) n} →
        {a : Tm Γ (A [ ⟨ true ⟩ ]T)} {b : Tm Γ (A [ ⟨ false ⟩ ]T)} →
        {c : Tm Γ Bool} {γ : Sub Δ Γ}
        {Γ∙ : Con∙ Γ} {Δ∙ : Con∙ Δ}
        {A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) n A} →
        {a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a} {b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b} →
        {c∙ : Tm∙ Γ∙ Bool∙ c} {γ∙ : Sub∙ Δ∙ Γ∙ γ} →
        let wt = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _ _) $ Bool[] $ true[])
            wf = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _ _) $ Bool[] $ false[])
            wc = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _ _) $ Bool[] $ coh)
        in
        elim∙ A∙ a∙ b∙ c∙ [ γ∙ ]t∙
          ~[ cong Tm∙ₑ $ refl $ refl $ weave wc $ refl $ weave∙ wc (⟨⟩∘∙ ∙ cong ∘∙ₑ $ refl $ refl $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _ _) $ Bool[] $ Bool[]∙) $ refl $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ refl $ Bool[] $ coh) $ coh $ (cong (⟨⟩∙ₑ _ _ _) $ Bool[] $ Bool[]∙ $ coh $ coh)) $ elim[] ]
        elim∙
          (A∙ [ coe (cong Sub∙ₑ $ (cong (_ ▹_) $ Bool[]) $ refl $ (cong (▹∙ₑ _ _ _) $ Bool[] $ Bool[]∙) $ refl $ coh) (γ∙ ⁺∙) ]T∙)
          (coe
            (cong Tm∙ₑ $ refl $ refl $ weave wt $ refl $ weave∙ wt (⟨⟩∘∙ ∙ cong ∘∙ₑ $ refl $ refl $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _ _) $ Bool[] $ Bool[]∙) $ refl $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ refl $ Bool[] $ true[]) $ coh $ (cong ⟨⟩∙ₑ $ refl $ refl $ refl $ Bool[] $ Bool[]∙ $ true[] $ true[]∙)) $ coh)
            (a∙ [ γ∙ ]t∙))
          (coe
            (cong Tm∙ₑ $ refl $ refl $ weave wf $ refl $ weave∙ wf (⟨⟩∘∙ ∙ cong ∘∙ₑ $ refl $ refl $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _ _) $ Bool[] $ Bool[]∙) $ refl $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ refl $ Bool[] $ false[]) $ coh $ (cong ⟨⟩∙ₑ $ refl $ refl $ refl $ Bool[] $ Bool[]∙ $ false[] $ false[]∙)) $ coh)
            (b∙ [ γ∙ ]t∙))
          (coe
            (cong (Tm∙ₑ _ _) $ Bool[] $ refl $ Bool[]∙ $ coh)
            (c∙ [ γ∙ ]t∙))
      Boolβ₁∙  : elim∙ A∙ a∙ b∙ true∙ ~[ cong (Tm∙ _ _) $ Boolβ₁ ] a∙
      Boolβ₂∙  : elim∙ A∙ a∙ b∙ false∙ ~[ cong (Tm∙ _ _) $ Boolβ₂ ] b∙

record DepModel {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    sorts∙ : Sorts∙ i j k j
    cwf∙   : CwF∙ sorts∙
    liftT∙ : LiftT∙ sorts∙ cwf∙
    uT∙    : UT∙ sorts∙ cwf∙
    pi∙    : Pi∙ sorts∙ cwf∙
    bool∙  : BoolT∙ sorts∙ cwf∙

  open Sorts∙ sorts∙ public
  open CwF∙ cwf∙ public
  open Pi∙ pi∙ public
  open BoolT∙ bool∙ public

module _ {i}{j}{k}(D : DepModel {i} {j} {k}) where

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
    ⟦◇⟧ : ⟦ ◇ ⟧Con     ↝ ◇∙
    ⟦▹⟧ : ⟦ Γ ▹ A ⟧Con ↝ ⟦ Γ ⟧Con ▹∙ ⟦ A ⟧Ty

    {-# REWRITE ⟦◇⟧ ⟦▹⟧ #-}
{-
    ⟦∘⟧   : ⟦ γ ∘ δ ⟧Sub ↝ ⟦ γ ⟧Sub ∘∙ ⟦ δ ⟧Sub
    ⟦id⟧  : ⟦ id {Γ = Γ} ⟧Sub ↝ id∙
    ⟦ε⟧   : ⟦ ε {Γ = Γ} ⟧Sub ↝ ε∙

    ⟦[]T⟧ : ⟦ A [ γ ]T ⟧Ty ↝ ⟦ A ⟧Ty [ ⟦ γ ⟧Sub ]T∙

    {-# REWRITE ⟦∘⟧ ⟦id⟧ ⟦ε⟧ ⟦[]T⟧ #-}

    ⟦[]t⟧ : ⟦ a [ γ ]t ⟧Tm ↝ ⟦ a ⟧Tm [ ⟦ γ ⟧Sub ]t∙
    ⟦p⟧   : ⟦ p {Γ = Γ} {A = A} ⟧Sub ↝ p∙

    {-# REWRITE ⟦[]t⟧ ⟦p⟧ #-}

    ⟦q⟧   : ⟦ q {Γ = Γ} {A = A} ⟧Tm ↝ q∙
    ⟦⁺⟧   : ⟦ _⁺ {Γ = Γ} {A = A} γ ⟧Sub ↝ ⟦ γ ⟧Sub ⁺∙
    ⟦⟨⟩⟧  : ⟦ ⟨ a ⟩ ⟧Sub ↝ ⟨ ⟦ a ⟧Tm ⟩∙
    
    {-# REWRITE ⟦q⟧ ⟦⁺⟧ ⟦⟨⟩⟧ #-}

    ⟦Π⟧ : ⟦ Π A B ⟧Ty ↝ Π∙ ⟦ A ⟧Ty ⟦ B ⟧Ty
    
    {-# REWRITE ⟦Π⟧ #-}

    ⟦lam⟧ : ⟦ lam b ⟧Tm ↝ lam∙ ⟦ b ⟧Tm
    ⟦app⟧ : ⟦ app f a ⟧Tm ↝ app∙ ⟦ f ⟧Tm ⟦ a ⟧Tm

    {-# REWRITE ⟦lam⟧ ⟦app⟧ #-}

    ⟦Bool⟧ : ⟦ Bool {Γ = Γ} ⟧Ty ↝ Bool∙
    
    {-# REWRITE ⟦Bool⟧ #-}

    ⟦true⟧ : ⟦ true {Γ = Γ} ⟧Tm ↝ true∙
    ⟦false⟧ : ⟦ false {Γ = Γ} ⟧Tm ↝ false∙

    {-# REWRITE ⟦true⟧ ⟦false⟧ #-}
    
    ⟦elim⟧ : ⟦ elim {Γ = Γ} A a b c ⟧Tm ↝ elim∙ ⟦ A ⟧Ty ⟦ a ⟧Tm ⟦ b ⟧Tm ⟦ c ⟧Tm

    {-# REWRITE ⟦elim⟧ #-}

    -- Without democracy, Ty, Sub, Tm can be injective
    Ty-inj : Ty Γ ≈ Ty Δ → Γ ≈ Δ

    Sub-inj₁ : Sub Δ Γ ≈ Sub Δ' Γ' → Δ ≈ Δ'
    Sub-inj₂ : Sub Δ Γ ≈ Sub Δ' Γ' → Γ ≈ Γ'

    Tm-inj₁ : Tm Γ A ≈ Tm Γ' B → Γ ≈ Γ'
    Tm-inj₂ : (e : Tm Γ A ≈ Tm Γ' B) → A ~[ cong Ty $ Tm-inj₁ e ] B

    -- Rules with coe
    ⟦Ty-coe⟧  : {e : Ty Γ ≈ Ty Δ} → ⟦ coe e A ⟧Ty ↝ coe (cong Ty∙ₑ $ Ty-inj e $ (cong ⟦_⟧Con $ Ty-inj e) $ coh) ⟦ A ⟧Ty
    ⟦Sub-coe⟧ : {e : Sub Δ Γ ≈ Sub Δ' Γ'}
              → let e1 = Sub-inj₁ e
                    e2 = Sub-inj₂ e
                in ⟦ coe e γ ⟧Sub ↝ coe (cong Sub∙ₑ $ e1 $ e2 $ (cong ⟦_⟧Con $ e1) $ (cong ⟦_⟧Con $ e2) $ coh) ⟦ γ ⟧Sub
    ⟦Tm-coe⟧  : {e : Tm Γ A ≈ Tm Δ B}
              → let e1 = Tm-inj₁ e
                    e2 = Tm-inj₂ e
                in ⟦ coe e a ⟧Tm ↝ coe (cong Tm∙ₑ $ e1 $ e2 $ (cong ⟦_⟧Con $ e1) $ (cong ⟦⟧Tyₑ $ e1 $ e2) $ coh) ⟦ a ⟧Tm
-- -} -- -} -- -} -- -} -- -} -- -}
