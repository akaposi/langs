{-# OPTIONS --prop --rewriting --with-K #-}

module Model where

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
    []t : (A : Ty Γ) → Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
    []t = λ A a γ → _[_]t {A = A} a γ

    [p][⟨⟩]T : A [ p ]T [ ⟨ a ⟩ ]T ≈ A
    [p][⟨⟩]T {A = A} = sym [∘]T ∙ cong (A [_]T) $ p∘⟨⟩ ∙ [id]T

    [p][⁺]T : A [ p ]T [ γ ⁺ ]T ~[ cong (Ty (Δ ▹ A [ γ ]T)) ] A [ γ ]T [ p ]T
    [p][⁺]T {A = A} = sym [∘]T ∙ cong (A [_]T) $ p∘⁺ ∙ [∘]T

    [▹η]T : A ≈ A [ p ⁺ ]T [ ⟨ q ⟩ ]T
    [▹η]T {A = A} = sym [id]T ∙ cong (A [_]T) $ ▹η ∙ [∘]T

    [⟨⟩][]T : A [ ⟨ a ⟩ ]T [ γ ]T ≈ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
    [⟨⟩][]T {A = A} = sym [∘]T ∙ cong (A [_]T) $ ⟨⟩∘ ∙ [∘]T

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
      ,[] : (a , b) [ γ ]t ~[ cong (Tm _) $ Σ[] ] (a [ γ ]t , coe (cong (Tm _) $ (sym [∘]T ∙ cong (B [_]T) $ ⟨⟩∘ ∙ [∘]T)) (b [ γ ]t))
      fst : Tm Γ (Σ A B) → Tm Γ A
      snd : (w : Tm Γ (Σ A B)) → Tm Γ (B [ ⟨ fst w ⟩ ]T)
      Σβ₁ : fst (a , b) ≈ a
      Σβ₂ : snd (a , b) ~[ cong (Tm _) $ (cong (B [_]T) $ (cong ⟨_⟩ $ Σβ₁)) ] b
      Ση  : {w : Tm Γ (Σ A B)} → w ≈ (fst w , snd w)

    tt[] : tt [ γ ]t ~[ cong (Tm _) $ ⊤[] ] tt
    tt[] {γ = γ} = sym coh ∙ ⊤η {a = coe (cong (Tm _) $ ⊤[]) (tt [ γ ]t)}

    infixr 4 _,≈_
    _,≈_ : (e1 : a ≈ b) → c ~[ cong (Tm _) $ (cong (λ x → A [ ⟨ x ⟩ ]T) $ e1) ] d → a , c ≈ b , d
    e1 ,≈ e2 = cong _,_ $ e1 $ e2
    
    fst[] : fst a [ γ ]t ≈ fst (coe (cong (Tm _) $ Σ[]) (a [ γ ]t))
    fst[] {a = a} {γ = γ} = sym (cong fst $ (coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) ∙ Σβ₁)

    snd[] : snd a [ γ ]t ~[ cong (Tm _) $ ([⟨⟩][]T ∙ cong (λ x → A [ γ ⁺ ]T [ ⟨ x ⟩ ]T) $ fst[]) ] snd (coe (cong (Tm _) $ Σ[]) (a [ γ ]t))
    snd[] {a = a} {γ = γ} = sym (cong snd $ (coh ∙ cong _[ γ ]t $ Ση ∙ ,[]) ∙ Σβ₂ ∙ coh)

module _ {i j k}(𝕊 : Sorts i j k j)(ℂ : CwF 𝕊)(⅀ : Sigma 𝕊 ℂ) where
  open Sorts 𝕊
  open CwF ℂ
  open Sigma ⅀

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
        (coe un-Sub γ , coe (cong (Tm _) $ (cong (A [_]T) $ ((sym coh ∙ sym q[⟨⟩] ∙ cong []t $ K[] $ (sym coh ∙ sym coh) $ refl) ∙ sym un-∘) ∙ [∘]T)) a)

record Model {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    sorts : Sorts i j k j
    cwf   : CwF sorts
    sigma : Sigma sorts cwf
    dem   : Dem sorts cwf sigma

  open Sorts sorts public
  open CwF cwf public
  open Sigma sigma public
  open Dem dem public

open Model public
