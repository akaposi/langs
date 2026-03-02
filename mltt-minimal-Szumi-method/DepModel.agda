{-# OPTIONS --prop --rewriting --with-K --confluence-check #-}

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
    [p][⁺]T∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ p∘⁺ $ p∘⁺∙ ∙ [∘]T∙

    [p][⟨⟩]T∙ : A∙ [ p∙ ]T∙ [ ⟨ a∙ ⟩∙ ]T∙ ~[ cong (Ty∙ _) $ [p][⟨⟩]T ] A∙
    [p][⟨⟩]T∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ p∘⟨⟩ $ p∘⟨⟩∙ ∙ [id]T∙ 
    
    field
      q[⁺]∙   : q∙ [ γ∙ ⁺∙ ]t∙ ~[ cong Tm∙ₑ $ cong (Δ ▹ A [ γ ]T) $ [p][⁺]T $ cong (Δ∙ ▹∙ A∙ [ γ∙ ]T∙) $ [p][⁺]T∙ $ q[⁺] ] q∙
      q[⟨⟩]∙  : q∙ [ ⟨ a∙ ⟩∙ ]t∙ ~[ cong (λ x → Tm∙ₑ _ x Γ∙) $ [p][⟨⟩]T $ [p][⟨⟩]T∙ $ q[⟨⟩] ] a∙
      ▹η∙     : id∙ {Γ∙ = Γ∙ ▹∙ A∙} ~[ cong (Sub∙ _ _) $ ▹η ] p∙ ⁺∙ ∘∙ ⟨ q∙ ⟩∙
      
    []t∙ₑ = λ Γ Γ∙ A A∙ a Δ Δ∙ γ a∙ γ∙ → _[_]t∙ {Γ} {Γ∙} {A} {A∙} {a} {Δ} {Δ∙} {γ} a∙ γ∙

    ⟨⟩∙ₑ = λ Γ Γ∙ A A∙ a a∙ → ⟨_⟩∙ {Γ} {Γ∙} {A} {A∙} {a} a∙
    
    [▹η]T∙ : A∙ ~[ cong (Ty∙ _) $ [▹η]T ] A∙ [ p∙ ⁺∙ ]T∙ [ ⟨ q∙ ⟩∙ ]T∙
    [▹η]T∙ = sym [id]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ ▹η $ ▹η∙ ∙ [∘]T∙

    [⟨⟩][]T∙ : A∙ [ ⟨ a∙ ⟩∙ ]T∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ [⟨⟩][]T ] A∙ [ γ∙ ⁺∙ ]T∙ [ ⟨ a∙ [ γ∙ ]t∙ ⟩∙ ]T∙
    [⟨⟩][]T∙ = sym [∘]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ ⟨⟩∘ $ ⟨⟩∘∙ ∙ [∘]T∙

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
      ,[]∙ : (a∙ ,∙ b∙) [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) $ Σ[] $ refl $ Σ[]∙ $ ,[] ] (a∙ [ γ∙ ]t∙ ,∙ coe (cong (Tm∙ₑ Δ) $ [⟨⟩][]T $ Δ∙ ∎ $ [⟨⟩][]T∙ $ sym coh) (b∙ [ γ∙ ]t∙))
      fst∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a → Tm∙ Γ∙ A∙ (fst a)
      snd∙ : (w∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a) → Tm∙ Γ∙ (B∙ [ ⟨ fst∙ w∙ ⟩∙ ]T∙) (snd a)
      Σβ₁∙ : fst∙ (a∙ ,∙ b∙) ~[ cong (Tm∙ _ _) $ Σβ₁ ] a∙
      Σβ₂∙ : {A∙ : Ty∙ Γ∙ A}{a∙ : Tm∙ Γ∙ A∙ a}{B∙ : Ty∙ (Γ∙ ▹∙ A∙) B}{b∙ : Tm∙ Γ∙ (B∙ [ ⟨ a∙ ⟩∙ ]T∙) b}
           → snd∙ (a∙ ,∙ b∙)
               ~[ cong (Tm∙ₑ _) $ (cong (λ x → B [ ⟨ x ⟩ ]T) $ Σβ₁) $ refl $ (cong ([]T∙ₑ _ _ _ _ _ _) $ (cong ⟨_⟩ $ Σβ₁) $ (cong (⟨⟩∙ₑ _ _ _ _) $ Σβ₁ $ Σβ₁∙)) $ Σβ₂ ]
             b∙
      Ση∙  : {w∙ : Tm∙ Γ∙ (Σ∙ A∙ B∙) a} → w∙ ~[ cong (Tm∙ _ _ ) $ Ση ] (fst∙ w∙ ,∙ snd∙ w∙)

    tt[]∙ : tt∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ Δ) ⠀ ⊤[] ⠀ Δ∙ ∎ ⠀ ⊤[]∙ ⠀ tt[] ] tt∙
    tt[]∙ {γ∙ = γ∙} = sym coh ∙ ⊤η∙ {a∙ = coe (cong Tm∙ₑ $ refl $ ⊤[] $ refl $ ⊤[]∙ $ tt[]) (tt∙ [ γ∙ ]t∙)}

    infixr 4 _,≈∙_
    _,≈∙_ : (e1 : a∙ ≈ b∙) → c∙ ~[ cong Tm∙ₑ $ Γ ∎ $ B [ ⟨ a ⟩ ]T ∎ $ Γ∙ ∎ $ (cong (λ x → B∙ [ ⟨ x ⟩∙ ]T∙) $ e1) $ refl ] d∙ → a∙ ,∙ c∙ ≈ b∙ ,∙ d∙
    e1 ,≈∙ e2 = cong _,∙_ $ e1 $ e2

    fst∙ₑ = λ Γ Γ∙ A A∙ B B∙ a a∙ → fst∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {a} a∙
    
    fst[]∙ : fst∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ _ _) $ fst[] ] fst∙ (coe (cong Tm∙ₑ $ Δ ∎ $ Σ[] $ Δ∙ ∎ $ Σ[]∙ $ sym coh) (a∙ [ γ∙ ]t∙))
    fst[]∙ {Γ} {Γ∙} {A} {B} {a} {A∙} {B∙} {a∙} {Δ} {γ} {Δ∙} {γ∙} =
      sym (cong (fst∙ₑ _ _ _ _ _ _) $ (coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) $ (coh ∙ cong ([]t∙ₑ _ _ _ _) $ Ση $ Δ ∎ $ Δ∙ ∎ $ γ ∎ $ Ση∙ $ γ∙ ∎ ∙ ,[]∙) ∙ Σβ₁∙)

    snd∙ₑ = λ Γ Γ∙ A A∙ B B∙ b b∙ → snd∙ {Γ} {Γ∙} {A} {A∙} {B} {B∙} {b} b∙

    snd[]∙ : snd∙ a∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ ([⟨⟩][]T ∙ cong (λ x → A [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) $ refl $ ([⟨⟩][]T∙ ∙ cong ([]T∙ₑ _ _ _ _ _ _) $ (cong ⟨_⟩ $ fst[]) $ (cong (⟨⟩∙ₑ _ _ _ _) $ fst[] $ fst[]∙)) $ snd[] ] snd∙ (coe (cong Tm∙ₑ $ Δ ∎ $ Σ[] $ Δ∙ ∎ $ Σ[]∙ $ sym coh) (a∙ [ γ∙ ]t∙))
    snd[]∙ {Γ} {Γ∙} {A} {B} {a} {A∙} {B∙} {a∙} {Δ} {γ} {Δ∙} {γ∙} =
      sym (cong (snd∙ₑ _ _ _ _ _ _) $ (coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) $ (coh ∙ cong ([]t∙ₑ _ _ _ _) ⠀ Ση ⠀ refl ⠀ refl ⠀ refl $ Ση∙ $ refl ∙ ,[]∙) ∙ Σβ₂∙ ∙ coh)

module _ {i j k}(𝕊 : Sorts∙ i j k j)(ℂ : CwF∙ 𝕊)(⅀ : Sigma∙ 𝕊 ℂ) where
  open Sorts∙ 𝕊
  open CwF∙ ℂ
  open Sigma∙ ⅀

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A
    
    Γ∙ Δ∙ Θ∙ Ξ∙ Ω∙ : Con∙ Γ
    γ∙ δ∙ θ∙ ξ∙ : Sub∙ {Δ = Δ} {Γ = Γ} Δ∙ Γ∙ γ
    A∙ B∙ C∙ : Ty∙ {Γ = Γ} Γ∙ A
    a∙ b∙ c∙ d∙ : Tm∙ {Γ = Γ} {A = A} Γ∙ A∙ a

  record Dem∙ : Set (i ⊔ lsuc j ⊔ k) where
    field
      K∙      : Con∙ Γ → Ty∙ Δ∙ (K Γ)
      K[]∙    : K∙ Ω∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ K[] ] K∙ Ω∙
      un-Sub∙ : Sub∙ Δ∙ Γ∙ γ ≈ Tm∙ Δ∙ (K∙ Γ∙) (coe un-Sub γ)
      un-∘∙   : γ∙ ∘∙ δ∙ ~[ un-Sub∙ ∙ cong Tm∙ₑ $ Θ ∎ $ sym K[] $ Θ∙ ∎ $ sym K[]∙ $ (coh ∙ un-∘) ] coe un-Sub∙ γ∙ [ δ∙ ]t∙
      un-◇∙   : K∙ {Δ∙ = Δ∙} ◇∙ ~[ cong (Ty∙ _) $ un-◇ ] ⊤∙
      un-▹∙   : K∙ {Δ∙ = Δ∙} (Ω∙ ▹∙ A∙) ~[ cong (Ty∙ _) $ un-▹ ] Σ∙ (K∙ Ω∙) (A∙ [ coe (cong Tm∙ₑ $ refl $ K[] $ refl $ K[]∙ $ (sym coh ∙ sym coh) ∙ sym un-Sub∙) q∙ ]T∙)
      un-,∙   : {γ∙ : Sub∙ Δ∙ Γ∙ γ}{a∙ : Tm∙ Δ∙ (A∙ [ γ∙ ]T∙) a} →
        γ∙ ⁺∙ ∘∙ ⟨ a∙ ⟩∙ ~[ un-Sub∙ ∙ cong Tm∙ₑ $ refl $ un-▹ $ refl $ un-▹∙ $ (coh ∙ un-,) ]
        let pr1 = (sym coh ∙ sym q[⟨⟩] ∙ cong ([]tₑ _ _) $ K[] $ (sym coh ∙ sym coh) $ refl ∙ sym un-∘)
        in (coe un-Sub∙ γ∙ ,∙ coe (cong (Tm∙ₑ _) $ (cong (A [_]T) $ pr1 ∙ [∘]T) $ refl $ (cong ([]T∙ₑ _ _ _ _ _ _) $ pr1 $ (sym coh ∙ sym q[⟨⟩]∙ ∙ cong ([]t∙ₑ _ _) $ K[] $ K[]∙ $ (sym coh ∙ sym coh) $ refl $ refl $ refl $ (sym coh ∙ sym coh) $ refl ∙ sym un-∘∙) ∙ [∘]T∙) $ sym coh) a∙)

record DepModel {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    sorts∙ : Sorts∙ i j k j
    cwf∙   : CwF∙ sorts∙
    sigma∙ : Sigma∙ sorts∙ cwf∙
    dem∙   : Dem∙ sorts∙ cwf∙ sigma∙

  open Sorts∙ sorts∙ public
  open CwF∙ cwf∙ public
  open Sigma∙ sigma∙ public
  open Dem∙ dem∙ public

module _ {i}{j}{k}(D : DepModel {i} {j} {k}) where

  open DepModel D

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c : Tm Γ A

  postulate
    ⟦_⟧Con : (Γ : Con) → Con∙ Γ
    ⟦_⟧Sub : (γ : Sub Δ Γ) → Sub∙ ⟦ Δ ⟧Con ⟦ Γ ⟧Con γ
    ⟦_⟧Ty  : (A : Ty Γ) → Ty∙ ⟦ Γ ⟧Con A
    ⟦_⟧Tm  : (a : Tm Γ A) → Tm∙ ⟦ Γ ⟧Con ⟦ A ⟧Ty a

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

    ⟦K⟧ : ⟦ K {Γ = Γ} Δ ⟧Ty ↝ K∙ ⟦ Δ ⟧Con

    {-# REWRITE ⟦snd⟧ ⟦K⟧ #-}
