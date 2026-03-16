{-# OPTIONS --prop --rewriting --with-K #-}

module BaseModel where

open import Lib

record Sorts i j k l : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  field
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
    infixl 8 _∘_
    infixl 5 _▹_
    infixl 9 _[_]T _[_]t
    infixl 10 _⁺
    infixl 11 ⟨_⟩
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
      [∘]t   : a [ γ ∘ δ ]t ~[ cong (Tm Θ) $ [∘]T ] a [ γ ]t [ δ ]t
      [id]t  : a [ id ]t ~[ cong (Tm Γ) $ [id]T ] a
      _▹_    : (Γ : Con) → Ty Γ → Con
      p      : Sub (Γ ▹ A) Γ
      q      : Tm  (Γ ▹ A) (A [ p ]T)
      _⁺     : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
      ∘⁺     : (γ ∘ δ) ⁺ ~[ cong Sub $ (cong (Θ ▹_) $ [∘]T {A = A}) $ refl ] γ ⁺ ∘ δ ⁺
      id⁺    : id ⁺ ~[ cong Sub $ (cong (Γ ▹_) $ [id]T {A = A}) $ refl ] id
      ⟨_⟩    : Tm Γ A → Sub Γ (Γ ▹ A)
      ⟨⟩∘    : ⟨ a ⟩ ∘ γ ≈ γ ⁺ ∘ ⟨ a [ γ ]t ⟩
      p∘⁺    : p {A = A} ∘ γ ⁺ ≈ γ ∘ p
      p∘⟨⟩   : p ∘ ⟨ a ⟩ ≈ id
      q[⁺]   : q [ γ ⁺ ]t ~[ cong (Tm _) $ (sym [∘]T ∙ cong (A [_]T) $ p∘⁺ ∙ [∘]T) ] q
      q[⟨⟩]  : q [ ⟨ a ⟩ ]t ~[ cong (Tm _) $ (sym [∘]T ∙ cong (A [_]T) $ p∘⟨⟩ ∙ [id]T) ] a
      ▹η     : id {Γ ▹ A} ≈ p ⁺ ∘ ⟨ q ⟩

    ∘ₑ = λ Γ Δ Θ γ δ → _∘_ {Δ} {Γ} {Θ} γ δ

    []Tₑ = λ Γ Δ A γ → _[_]T {Γ} {Δ} A γ

    []tₑ = λ Γ Δ A a γ → _[_]t {Γ = Γ} {A = A} {Δ = Δ} a γ

    ⟨⟩ₑ = λ Γ A a → ⟨_⟩ {Γ} {A} a

    ⁺ₑ = λ Γ Δ A γ → _⁺ {Δ} {Γ} {A} γ

    weave : {γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ} → γ ∘ δ ≈ γ' ∘ δ' → A [ γ ]T [ δ ]T ≈ A [ γ' ]T [ δ' ]T
    weave e = sym [∘]T ∙ cong (_ [_]T) $ e ∙ [∘]T
    -- Name inspired by 1Lab

    annihilate : γ ∘ δ ≈ id → A [ γ ]T [ δ ]T ≈ A
    annihilate e = sym [∘]T ∙ cong (_ [_]T) $ e ∙ [id]T
    -- Name inspired by 1Lab

    [p][⟨⟩]T : A [ p ]T [ ⟨ a ⟩ ]T ≈ A
    [p][⟨⟩]T = annihilate p∘⟨⟩

    [p][⁺]T : A [ p ]T [ γ ⁺ ]T ~[ cong (Ty (Δ ▹ A [ γ ]T)) ] A [ γ ]T [ p ]T
    [p][⁺]T = weave p∘⁺

    [▹η]T : A ≈ A [ p ⁺ ]T [ ⟨ q ⟩ ]T
    [▹η]T = sym (annihilate (sym ▹η))

    [⟨⟩][]T : A [ ⟨ a ⟩ ]T [ γ ]T ≈ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
    [⟨⟩][]T = weave ⟨⟩∘

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d : Tm Γ A

  record Sigma : Set (i ⊔ j ⊔ k ⊔ l) where
    infixr 5 _,_
    field
      ⊤   : Ty Γ
      ⊤[] : ⊤ [ γ ]T ≈ ⊤
      tt  : Tm Γ ⊤
      ⊤η  : a ≈ tt
      Σ   : (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
      Σ[] : Σ A B [ γ ]T ≈ Σ (A [ γ ]T) (B [ γ ⁺ ]T)
      _,_ : (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T) → Tm Γ (Σ A B)
      ,[] : (a , b) [ γ ]t ~[ cong (Tm _) $ Σ[] ] (a [ γ ]t , coe (cong (Tm _) $ [⟨⟩][]T) (b [ γ ]t))
      fst : Tm Γ (Σ A B) → Tm Γ A
      snd : (w : Tm Γ (Σ A B)) → Tm Γ (B [ ⟨ fst w ⟩ ]T)
      Σβ₁ : fst (a , b) ≈ a
      Σβ₂ : snd (a , b) ~[ cong (Tm _) $ (cong (B [_]T) $ (cong ⟨_⟩ $ Σβ₁)) ] b
      Ση  : {w : Tm Γ (Σ A B)} → w ≈ (fst w , snd w)

    tt[] : tt [ γ ]t ~[ cong (Tm _) $ ⊤[] ] tt
    tt[] {γ = γ} = coh ∙ ⊤η {a = coe (cong (Tm _) $ ⊤[]) (tt [ γ ]t)}

    infixr 4 _,≈_
    _,≈_ : (e1 : a ≈ b) → c ~[ cong (Tm _) $ (cong (λ x → A [ ⟨ x ⟩ ]T) $ e1) ] d → a , c ≈ b , d
    e1 ,≈ e2 = cong _,_ $ e1 $ e2
    
    fst[] : fst a [ γ ]t ≈ fst (coe (cong (Tm _) $ Σ[]) (a [ γ ]t))
    fst[] {a = a} {γ = γ} = sym (cong fst $ (sym coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) ∙ Σβ₁)

    snd[] : snd a [ γ ]t ~[ cong (Tm _) $ ([⟨⟩][]T ∙ cong (λ x → A [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) ] snd (coe (cong (Tm _) $ Σ[]) (a [ γ ]t))
    snd[] {a = a} {γ = γ} = sym (cong snd $ (sym coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) ∙ Σβ₂ ∙ sym coh)

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d f : Tm Γ A

  record Pi : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 9 _[_]Π
    field
      Π     : (A : Ty Γ)(B : Ty (Γ ▹ A)) → Ty Γ
      Π[]   :  Π A B [ γ ]T ≈ Π (A [ γ ]T) (B [ γ ⁺ ]T)
    
    _[_]Π : (f : Tm Γ (Π A B))(γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
    f [ γ ]Π = coe (cong (Tm _) $ Π[]) (f [ γ ]t)

    []Π   : a [ γ ]t ~[ cong (Tm _) $ Π[] ] a [ γ ]Π
    []Π = coh

    field
      lam   : (t : Tm (Γ ▹ A) B) → Tm Γ (Π A B)
      app   : (f : Tm Γ (Π A B))(a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
      Πβ    : app (lam b) a ≈ b [ ⟨ a ⟩ ]t
      Πη    : lam (app (f [ p ]Π) q) ~[ cong (Tm _) $ (cong (Π _) $ sym [▹η]T) ] f
      lam[] : lam b [ γ ]t ~[ cong (Tm _) $ Π[] ] lam (b [ γ ⁺ ]t)
      app[] : app f a [ γ ]t ~[ cong (Tm _) $ [⟨⟩][]T ] app (f [ γ ]Π) (a [ γ ]t)

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d f : Tm Γ A

  record Empty : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      ⊥         : Ty Γ
      ⊥[]       : ⊥ [ γ ]T ≈ ⊥
      exfalso   : Tm Γ ⊥ → Tm Γ A
      exfalso[] : exfalso {A = A} a [ γ ]t ≈ exfalso (coe (cong (Tm _) $ ⊥[]) (a [ γ ]t))

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ
    a b c d f : Tm Γ A

  record BoolT : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      Bool    : Ty Γ
      Bool[]  : Bool [ γ ]T ≈ Bool
      true    : Tm Γ Bool
      false   : Tm Γ Bool
      true[]  : true [ γ ]t ~[ cong (Tm _) $ Bool[] ] true
      false[] : false [ γ ]t ~[ cong (Tm _) $ Bool[] ] false
      elim    : (A : Ty (Γ ▹ Bool)) → Tm Γ (A [ ⟨ true ⟩ ]T) → Tm Γ (A [ ⟨ false ⟩ ]T) → (b : Tm Γ Bool) → Tm Γ (A [ ⟨ b ⟩ ]T)
      elim[]  :
        {A : Ty (Γ ▹ Bool)} →
        {a : Tm Γ (A [ ⟨ true ⟩ ]T)} {b : Tm Γ (A [ ⟨ false ⟩ ]T)} →
        {c : Tm Γ Bool} {γ : Sub Δ Γ} →
        elim A a b c [ γ ]t
          ~[ cong (Tm _) $ weave (⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ coh)) ]
        elim
          (A [ coe (cong Sub $ (cong (_ ▹_) $ Bool[]) $ refl) (γ ⁺) ]T)
          (coe
            (cong (Tm _)
              $ weave (⟨⟩∘ ∙
                       (cong (∘ₑ _)
                          $ (cong (_ ▹_) $ Bool[]) $ refl
                          $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ true[]))))
            (a [ γ ]t))
          (coe
            (cong (Tm _)
              $ weave (⟨⟩∘ ∙
                       (cong (∘ₑ _)
                          $ (cong (_ ▹_) $ Bool[]) $ refl
                          $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ false[]))))
            (b [ γ ]t))
          (coe (cong (Tm _) $ Bool[]) (c [ γ ]t))
      Boolβ₁  : elim A a b true ≈ a
      Boolβ₂  : elim A a b false ≈ b
      -- NOP -- Boolη   : f [ ⟨ true ⟩ ]t ≈ a → f [ ⟨ false ⟩ ]t ≈ b → f [ ⟨ c ⟩ ]t ≈ elim A a b c

record BaseModel {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    sorts : Sorts i j k j
    cwf   : CwF sorts
    sigma : Sigma sorts cwf
    pi    : Pi sorts cwf
    empty : Empty sorts cwf
    bool  : BoolT sorts cwf

  open Sorts sorts public
  open CwF cwf public
  open Sigma sigma public
  open Pi pi public
  open Empty empty public
  open BoolT bool public

open BaseModel public
