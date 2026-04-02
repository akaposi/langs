{-# OPTIONS --prop --rewriting --with-K --confluence-check #-}

module Dictatorship.DepModel where

open import Lib
open import Dictatorship.Syntax
import Dictatorship.Model as M

module I = M.Model I
open I

record Sorts∙ i j k l : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  field
    Con∙ : Con → Set i
    Sub∙ : {Δ Γ : Con}(Δ∙ : Con∙ Δ)(Γ∙ : Con∙ Γ)(γ : Sub Δ Γ) → Set j
    Ty∙  : {Γ : Con}(Γ∙ : Con∙ Γ)(A : Ty Γ) → Set k
    Tm∙  : {Γ : Con}{A : Ty Γ}(Γ∙ : Con∙ Γ)(A∙ : Ty∙ Γ∙ A)(t : Tm Γ A) → Set l

  Sub∙ₑ = λ Δ Γ Δ∙ Γ∙ γ → Sub∙ {Δ} {Γ} Δ∙ Γ∙ γ
  Ty∙ₑ = λ Γ Γ∙ A → Ty∙ {Γ} Γ∙ A
  Tm∙ₑ = λ Γ A Γ∙ A∙ a → Tm∙ {Γ} {A} Γ∙ A∙ a

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
      ◇η∙     : {γ∙ : Sub∙ Γ∙ ◇∙ γ} → γ∙ ~[ cong (Sub∙ _ _) $ ◇η ] ε∙
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

    weave∙ : {A : Ty Γ}{γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ}
             {A∙ : Ty∙ Γ∙ A}{γ∙ : Sub∙ Ξ∙ Γ∙ γ}{δ∙ : Sub∙ Θ∙ Ξ∙ δ}{γ'∙ : Sub∙ Δ∙ Γ∙ γ'}{δ'∙ : Sub∙ Θ∙ Δ∙ δ'}
             (e : γ ∘ δ ≈ γ' ∘ δ')(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] γ'∙ ∘∙ δ'∙)
           → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _) $ weave e ] A∙ [ γ'∙ ]T∙ [ δ'∙ ]T∙
    weave∙ e e∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ e $ e∙ ∙ [∘]T∙

    annihilate∙ : (e : γ ∘ δ ≈ id)(e∙ : γ∙ ∘∙ δ∙ ~[ cong (Sub∙ _ _) $ e ] id∙ {Γ∙ = Γ∙})
                → A∙ [ γ∙ ]T∙ [ δ∙ ]T∙ ~[ cong (Ty∙ _) $ annihilate e ] A∙
    annihilate∙ e e∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ e $ e∙ ∙ [id]T∙

    [p][⁺]T∙ : A∙ [ p∙ ]T∙ [ γ∙ ⁺∙ ]T∙ ~[ cong (Ty∙ (Δ∙ ▹∙ A∙ [ γ∙ ]T∙)) $ [p][⁺]T ] A∙ [ γ∙ ]T∙ [ p∙ ]T∙
    [p][⁺]T∙ = weave∙ p∘⁺ p∘⁺∙

    [p][⟨⟩]T∙ : A∙ [ p∙ ]T∙ [ ⟨ a∙ ⟩∙ ]T∙ ~[ cong (Ty∙ _) $ [p][⟨⟩]T ] A∙
    [p][⟨⟩]T∙ = annihilate∙ p∘⟨⟩ p∘⟨⟩∙
    
    field
      q[⁺]∙   : q∙ [ γ∙ ⁺∙ ]t∙ ~[ cong Tm∙ₑ $ cong (Δ ▹ A [ γ ]T) $ [p][⁺]T $ cong (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) $ [p][⁺]T∙ $ q[⁺] ] q∙
      q[⟨⟩]∙  : q∙ [ ⟨ a∙ ⟩∙ ]t∙ ~[ cong (λ x → Tm∙ₑ _ x Γ∙) $ [p][⟨⟩]T $ [p][⟨⟩]T∙ $ q[⟨⟩] ] a∙
      ▹η∙     : id∙ {Γ∙ = Γ∙ ▹∙ A∙} ~[ cong (Sub∙ _ _) $ ▹η ] p∙ ⁺∙ ∘∙ ⟨ q∙ ⟩∙
      
    []t∙ₑ = λ Γ Γ∙ A A∙ a Δ Δ∙ γ a∙ γ∙ → _[_]t∙ {Γ} {Γ∙} {A} {A∙} {a} {Δ} {Δ∙} {γ} a∙ γ∙

    ⟨⟩∙ₑ = λ Γ Γ∙ A A∙ a a∙ → ⟨_⟩∙ {Γ} {Γ∙} {A} {A∙} {a} a∙

    ∘∙ₑ = λ Γ Γ∙ Δ Δ∙ Θ Θ∙ γ δ γ∙ δ∙ → _∘∙_ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {Θ} {Θ∙} {δ} γ∙ δ∙

    ⁺∙ₑ = λ Γ Γ∙ Δ Δ∙ A A∙ γ γ∙  → _⁺∙ {Δ} {Δ∙} {Γ} {Γ∙} {γ} {A} {A∙} γ∙

    ▹∙ₑ = λ Γ Γ∙ A A∙ → _▹∙_ {Γ} {A} Γ∙ A∙

    p∙ₑ = λ Γ Γ∙ A A∙ → p∙ {Γ} {Γ∙} {A} {A∙}

    q∙ₑ = λ Γ Γ∙ A A∙ → q∙ {Γ} {Γ∙} {A} {A∙}

    [▹η]T∙ : A∙ ~[ cong (Ty∙ _) $ [▹η]T ] A∙ [ p∙ ⁺∙ ]T∙ [ ⟨ q∙ ⟩∙ ]T∙
    [▹η]T∙ = sym (annihilate∙ (sym ▹η) (sym ▹η∙))

    [⟨⟩][]T∙ : A∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ [⟨⟩][]T ] A∙ [ γ∙ ⁺∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙
    [⟨⟩][]T∙ = weave∙ ⟨⟩∘ ⟨⟩∘∙

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ d∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record Sigma∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    infixr 5 _,∙_
    field
      ⊤∙   : Ty∙ Γ∙ ⊤
      ⊤[]∙ : ⊤∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊤[] ] ⊤∙
      tt∙  : Tm∙ Γ∙ ⊤∙ tt
      ⊤η∙  : a∙ ~[ cong Tm∙ₑ $ Γ ∎ $ refl $ Γ∙ ∎ $ refl $ ⊤η ] tt∙
      Σ∙   : (A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Σ A B)
      Σ[]∙ : Σ∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Σ[] ] Σ∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)
      _,∙_ : (a∙ : Tm∙ Γ∙ A∙ a)(b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b) → Tm∙ Γ∙ (Σ∙ A∙ B∙) (a , b)
      ,[]∙ : (a∙ ,∙ b∙) [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) $ Σ[] $ refl $ Σ[]∙ $ ,[] ] (a∙ [ γ∙ ]t∙ ,∙ coe (cong (Tm∙ₑ Δ) $ [⟨⟩][]T $ Δ∙ ∎ $ [⟨⟩][]T∙ $ coh) (b∙ [ γ∙ ]t∙))
      fst∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a → Tm∙ Γ∙ A∙ (fst a)
      snd∙ : (w∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a) → Tm∙ Γ∙ (B∙ [ ⟨ fst∙ w∙ ⟩∙ ]T∙) (snd a)
      Σβ₁∙ : fst∙ (a∙ ,∙ b∙) ~[ cong (Tm∙ _ _) $ Σβ₁ ] a∙
      Σβ₂∙ : {A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
           → snd∙ (a∙ ,∙ b∙)
               ~[ cong (Tm∙ₑ _) $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ refl $ (cong ([]T∙ₑ _ _ _ _ _ _) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ _) $ Σβ₁ $ Σβ₁∙)) $ Σβ₂ ]
             b∙
      Ση∙  : {w∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a} → w∙ ~[ cong (Tm∙ _ _ ) $ Ση ] (fst∙ w∙ ,∙ snd∙ w∙)

    tt[]∙ : tt∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) $ ⊤[] $ Δ∙ ∎ $ ⊤[]∙ $ tt[] ] tt∙
    tt[]∙ {γ∙ = γ∙} = coh ∙ ⊤η∙ {a∙ = coe (cong Tm∙ₑ $ refl $ ⊤[] $ refl $ ⊤[]∙ $ tt[]) (tt∙ [ γ∙ ]t∙)}

    infixr 4 _,≈∙_
    _,≈∙_ : (e1 : a∙ ≈ b∙) → c∙ ~[ cong Tm∙ₑ $ Γ ∎ $ B [ ⟨ a ⟩ ]T ∎ $ Γ∙ ∎ $ (cong (λ x → B∙ [ ⟨ x ⟩∙ ]T∙) $ e1) $ refl ] d∙ → a∙ ,∙ c∙ ≈ b∙ ,∙ d∙
    e1 ,≈∙ e2 = cong _,∙_ $ e1 $ e2

    fst∙ₑ = λ Γ Γ∙ A A∙ B B∙ a a∙ → fst∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {a} a∙
    
    fst[]∙ : fst∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ _ _) $ fst[] ] fst∙ (coe (cong Tm∙ₑ $ Δ ∎ $ Σ[] $ Δ∙ ∎ $ Σ[]∙ $ coh) (a∙ [ γ∙ ]t∙))
    fst[]∙ {Γ} {Γ∙} {A} {B} {a} {A∙} {B∙} {a∙} {Δ} {γ} {Δ∙} {γ∙} =
      sym (cong (fst∙ₑ _ _ _ _ _ _) $ (sym coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) $ (sym coh ∙ cong ([]t∙ₑ _ _ _ _) $ Ση $ Δ ∎ $ Δ∙ ∎ $ γ ∎ $ Ση∙ $ γ∙ ∎ ∙ ,[]∙) ∙ Σβ₁∙)

    snd∙ₑ = λ Γ Γ∙ A A∙ B B∙ b b∙ → snd∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {b} b∙

    snd[]∙ : snd∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ ([⟨⟩][]T ∙ cong (λ x → A [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) $ refl $ ([⟨⟩][]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ (cong ⟨_⟩ $ fst[]) $ (cong (⟨⟩∙ₑ _ _ _ _) $ fst[] $ fst[]∙)) $ snd[] ] snd∙ (coe (cong Tm∙ₑ $ Δ ∎ $ Σ[] $ Δ∙ ∎ $ Σ[]∙ $ coh) (a∙ [ γ∙ ]t∙))
    snd[]∙ {Γ} {Γ∙} {A} {B} {a} {A∙} {B∙} {a∙} {Δ} {γ} {Δ∙} {γ∙} =
      sym (cong (snd∙ₑ _ _ _ _ _ _) $ (sym coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) $ (sym coh ∙ cong ([]t∙ₑ _ _ _ _) $ Ση $ refl $ refl $ refl $ Ση∙ $ refl ∙ ,[]∙) ∙ Σβ₂∙ ∙ sym coh)

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record Pi∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 9 _[_]Π∙
    field
      Π∙     : (A∙ : Ty∙ Γ∙ A)(B∙ : Ty∙ (Γ∙ ▹∙ A∙) B) → Ty∙ Γ∙ (Π A B)
      Π[]∙   : Π∙ A∙ B∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Π[] ] Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)
    
    _[_]Π∙ : (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(γ∙ : Sub∙ Δ∙ Γ∙ γ) → Tm∙ Δ∙ (Π∙ (A∙ [ γ∙ ]T∙) (B∙ [ γ∙ ⁺∙ ]T∙)) (f [ γ ]Π)
    f∙ [ γ∙ ]Π∙ = coe (cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ $ []Π) (f∙ [ γ∙ ]t∙)

    []Π∙   : a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ $ []Π ] a∙ [ γ∙ ]Π∙
    []Π∙ = coh

    Π∙ₑ = λ Γ Γ∙ A A∙ B B∙ → Π∙ {Γ} {Γ∙} {A} {B} A∙ B∙

    field
      lam∙   : (b∙ : Tm∙ (Γ∙ ▹∙ A∙) B∙ b) → Tm∙ Γ∙ (Π∙ A∙ B∙) (lam b)
      app∙   : (f∙ : Tm∙ Γ∙ (Π∙ A∙ B∙) f)(a∙ : Tm∙ Γ∙ A∙ a) → Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) (app f a)
      Πβ∙    : app∙ (lam∙ b∙) a∙ ~[ cong (Tm∙ _ _) $ Πβ ] b∙ [ ⟨ a∙ ⟩∙ ]t∙
      Πη∙    : lam∙ (app∙ (f∙ [ p∙ ]Π∙) q∙) ~[ cong (Tm∙ₑ _) $ (cong (Π _) $ sym [▹η]T) $ refl $ (cong (Π∙ₑ _ _ _ _) $ sym [▹η]T $ sym [▹η]T∙) $ Πη ] f∙
      lam[]∙ : lam∙ b∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Π[] $ refl $ Π[]∙ $ lam[] ] lam∙ (b∙ [ γ∙ ⁺∙ ]t∙)
      app[]∙ : app∙ f∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ [⟨⟩][]T $ refl $ [⟨⟩][]T∙ $ app[] ] app∙ (f∙ [ γ∙ ]Π∙) (a∙ [ γ∙ ]t∙)

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record Empty∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      ⊥∙         : Ty∙ Γ∙ ⊥
      ⊥[]∙       : {γ∙ : Sub∙ Δ∙ Γ∙ γ} → ⊥∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ ⊥[] ] ⊥∙ {Γ∙ = Δ∙}
      exfalso∙   : (a∙ : Tm∙ Γ∙ ⊥∙ a) → Tm∙ {A = A} Γ∙ A∙ (exfalso a)
      exfalso[]∙ : exfalso∙ {A∙ = A∙} a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ _ _) $ exfalso[] ] exfalso∙ (coe (cong (Tm∙ₑ _) $ ⊥[] $ refl $ ⊥[]∙ $ coh) (a∙ [ γ∙ ]t∙))

module _ {i j k l}(𝕊 : Sorts∙ i j k l)(ℂ : CwF∙ 𝕊) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record BoolT∙ : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      Bool∙    : Ty∙ Γ∙ Bool
      Bool[]∙  : Bool∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Bool[] ] Bool∙
      true∙    : Tm∙ Γ∙ Bool∙ true
      false∙   : Tm∙ Γ∙ Bool∙ false
      true[]∙  : true∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Bool[] $ refl $ Bool[]∙ $ true[] ] true∙
      false[]∙ : false∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Bool[] $ refl $ Bool[]∙ $ false[] ] false∙
      elim∙    : {Γ : Con} {A : Ty (Γ ▹ Bool)}
                 {a : Tm Γ (A [ ⟨ true ⟩ ]T)}
                 {b : Tm Γ (A [ ⟨ false ⟩ ]T)}
                 {c : Tm Γ Bool}
                 {Γ∙ : Con∙ Γ}
                 (A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) A)
                 (a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a)
                 (b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b)
                 (c∙ : Tm∙ Γ∙ Bool∙ c)
               → Tm∙ Γ∙ (A∙ [ ⟨ c∙ ⟩∙ ]T∙) (elim A a b c)
      elim[]∙  :
        {Γ Δ : Con}
        {A : Ty (Γ ▹ Bool)} →
        {a : Tm Γ (A [ ⟨ true ⟩ ]T)} {b : Tm Γ (A [ ⟨ false ⟩ ]T)} →
        {c : Tm Γ Bool} {γ : Sub Δ Γ}
        {Γ∙ : Con∙ Γ} {Δ∙ : Con∙ Δ}
        {A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) A} →
        {a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a} {b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b} →
        {c∙ : Tm∙ Γ∙ Bool∙ c} {γ∙ : Sub∙ Δ∙ Γ∙ γ} →
        let wt = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ true[])
            wf = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ false[])
            wc = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ coh)
        in
        elim∙ A∙ a∙ b∙ c∙ [ γ∙ ]t∙
          ~[ cong (Tm∙ₑ _) $ weave wc $ refl $ weave∙ wc (⟨⟩∘∙ ∙ cong (∘∙ₑ _ _) $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙) $ refl $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ coh) $ coh $ (cong (⟨⟩∙ₑ _ _) $ Bool[] $ Bool[]∙ $ coh $ coh)) $ elim[] ]
        elim∙
          (A∙ [ coe (cong Sub∙ₑ $ (cong (_ ▹_) $ Bool[]) $ refl $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙) $ refl $ coh) (γ∙ ⁺∙) ]T∙)
          (coe
            (cong (Tm∙ₑ _) $ weave wt $ refl $ weave∙ wt (⟨⟩∘∙ ∙ cong (∘∙ₑ _ _) $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙) $ refl $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ true[]) $ coh $ (cong (⟨⟩∙ₑ _ _) $ Bool[] $ Bool[]∙ $ true[] $ true[]∙)) $ coh)
            (a∙ [ γ∙ ]t∙))
          (coe
            (cong (Tm∙ₑ _) $ weave wf $ refl $ weave∙ wf (⟨⟩∘∙ ∙ cong (∘∙ₑ _ _) $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙) $ refl $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ false[]) $ coh $ (cong (⟨⟩∙ₑ _ _) $ Bool[] $ Bool[]∙ $ false[] $ false[]∙)) $ coh)
            (b∙ [ γ∙ ]t∙))
          (coe
            (cong (Tm∙ₑ _) $ Bool[] $ refl $ Bool[]∙ $ coh)
            (c∙ [ γ∙ ]t∙))
      Boolβ₁∙  : elim∙ A∙ a∙ b∙ true∙ ~[ cong (Tm∙ _ _) $ Boolβ₁ ] a∙
      Boolβ₂∙  : elim∙ A∙ a∙ b∙ false∙ ~[ cong (Tm∙ _ _) $ Boolβ₂ ] b∙

record DepModel {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    sorts∙ : Sorts∙ i j k j
    cwf∙   : CwF∙ sorts∙
    sigma∙ : Sigma∙ sorts∙ cwf∙
    pi∙    : Pi∙ sorts∙ cwf∙
    empty∙ : Empty∙ sorts∙ cwf∙
    bool∙  : BoolT∙ sorts∙ cwf∙

  open Sorts∙ sorts∙ public
  open CwF∙ cwf∙ public
  open Sigma∙ sigma∙ public
  open Pi∙ pi∙ public
  open Empty∙ empty∙ public
  open BoolT∙ bool∙ public

module _ {i}{j}{k}(D : DepModel {i} {j} {k}) where

  open DepModel D

  private variable
    Γ Δ Γ' Δ' Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c f : Tm Γ A

    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ d∙ f∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  postulate
    ⟦_⟧Con : (Γ : Con) → Con∙ Γ
    ⟦_⟧Sub : (γ : Sub Δ Γ) → Sub∙ ⟦ Δ ⟧Con ⟦ Γ ⟧Con γ
    ⟦_⟧Ty  : (A : Ty Γ) → Ty∙ ⟦ Γ ⟧Con A
    ⟦_⟧Tm  : (a : Tm Γ A) → Tm∙ ⟦ Γ ⟧Con ⟦ A ⟧Ty a

  ⟦⟧Subₑ = λ Δ Γ γ → ⟦_⟧Sub {Δ} {Γ} γ
  ⟦⟧Tyₑ = λ Γ A → ⟦_⟧Ty {Γ} A
  ⟦⟧Tmₑ = λ Γ A a → ⟦_⟧Tm {Γ} {A} a

  postulate
    ⟦◇⟧ : ⟦ ◇ ⟧Con     ↝ ◇∙
    ⟦▹⟧ : ⟦ Γ ▹ A ⟧Con ↝ ⟦ Γ ⟧Con ▹∙ ⟦ A ⟧Ty

    {-# REWRITE ⟦◇⟧ ⟦▹⟧ #-}

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

    ⟦⊤⟧   : ⟦ ⊤ {Γ = Γ} ⟧Ty ↝ ⊤∙
    
    {-# REWRITE ⟦q⟧ ⟦⁺⟧ ⟦⟨⟩⟧ ⟦⊤⟧ #-}

    ⟦tt⟧  : ⟦ tt {Γ = Γ} ⟧Tm ↝ tt∙

    ⟦Σ⟧   : ⟦ Σ A B ⟧Ty ↝ Σ∙ ⟦ A ⟧Ty ⟦ B ⟧Ty

    {-# REWRITE ⟦tt⟧ ⟦Σ⟧ #-}
    
    ⟦,⟧   : ⟦ a , b ⟧Tm ↝ ⟦ a ⟧Tm ,∙ ⟦ b ⟧Tm
    ⟦fst⟧ : ⟦ fst a ⟧Tm ↝ fst∙ ⟦ a ⟧Tm

    {-# REWRITE ⟦,⟧ ⟦fst⟧ #-}

    ⟦snd⟧ : ⟦ snd {Γ = Γ} {A = A} {B = B} b ⟧Tm ↝ snd∙ ⟦ b ⟧Tm

    ⟦Π⟧ : ⟦ Π A B ⟧Ty ↝ Π∙ ⟦ A ⟧Ty ⟦ B ⟧Ty
    
    {-# REWRITE ⟦snd⟧ ⟦Π⟧ #-}

    ⟦lam⟧ : ⟦ lam b ⟧Tm ↝ lam∙ ⟦ b ⟧Tm
    ⟦app⟧ : ⟦ app f a ⟧Tm ↝ app∙ ⟦ f ⟧Tm ⟦ a ⟧Tm
    
    ⟦⊥⟧ : ⟦ ⊥ {Γ = Γ} ⟧Ty ↝ ⊥∙

    {-# REWRITE ⟦lam⟧ ⟦app⟧ ⟦⊥⟧ #-}

    ⟦exfalso⟧ : ⟦ exfalso {A = A} a ⟧Tm ↝ exfalso∙ ⟦ a ⟧Tm

    ⟦Bool⟧ : ⟦ Bool {Γ = Γ} ⟧Ty ↝ Bool∙
    
    {-# REWRITE ⟦exfalso⟧ ⟦Bool⟧ #-}

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
