{-# OPTIONS --prop --rewriting --with-K --confluence-check --hidden-argument-puns #-}

module Model where

open import Lib

record Sorts i j k l : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
  field
    Con : Set i
    Sub : Con → Con → Set j
    Ty  : Con → ℕ → Set k
    Tm  : (Γ : Con) → {n : ℕ} → Ty Γ n → Set l

module _ {i j k l}(𝕊 : Sorts i j k l) where
  open Sorts 𝕊

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c : Tm Γ A

  record CwF : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 8 _∘_
    infixl 5 _▹_
    infixl 9 _[_]T _[_]t
    infixl 10 _⁺
    infixl 11 ⟨_⟩
    field
      _∘_            : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
      instance ass   : (γ ∘ δ) ∘ θ ≈ γ ∘ (δ ∘ θ)
      id             : Sub Γ Γ
      instance idl   : id ∘ γ ≈ γ
      instance idr   : γ ∘ id ≈ γ
      ◇              : Con
      ε              : Sub Γ ◇
      instance ◇η    : γ ≈ ε
      _[_]T          : Ty Γ n → Sub Δ Γ → Ty Δ n
      instance [∘]T  : A [ γ ∘ δ ]T ≈ A [ γ ]T [ δ ]T
      instance [id]T : A [ id ]T ≈ A
      _[_]t          : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
      instance [∘]t  : a [ γ ∘ δ ]t ~[ cong (Tm Θ) $ [∘]T ] a [ γ ]t [ δ ]t
      instance [id]t : a [ id ]t ~[ cong (Tm Γ) $ [id]T ] a
      _▹_            : (Γ : Con) → Ty Γ n → Con
      p              : Sub (Γ ▹ A) Γ
      q              : Tm  (Γ ▹ A) (A [ p ]T)
      _⁺             : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
      instance ∘⁺    : (γ ∘ δ) ⁺ ~[ cong Sub $ (cong (Θ ▹_) $ [∘]T {A = A}) $ refl ] γ ⁺ ∘ δ ⁺
      instance id⁺   : id ⁺ ~[ cong Sub $ (cong (Γ ▹_) $ [id]T {A = A}) $ refl ] id
      ⟨_⟩            : Tm Γ A → Sub Γ (Γ ▹ A)
      instance ⟨⟩∘   : ⟨ a ⟩ ∘ γ ≈ γ ⁺ ∘ ⟨ a [ γ ]t ⟩
      instance p∘⁺   : p {A = A} ∘ γ ⁺ ≈ γ ∘ p
      instance p∘⟨⟩  : p ∘ ⟨ a ⟩ ≈ id
      instance q[⁺]  : q [ γ ⁺ ]t ~[ cong (Tm _) $ (sym [∘]T ∙ cong (A [_]T) $ p∘⁺ ∙ [∘]T) ] q
      instance q[⟨⟩] : q [ ⟨ a ⟩ ]t ~[ cong (Tm _) $ (sym [∘]T ∙ cong (A [_]T) $ p∘⟨⟩ ∙ [id]T) ] a
      instance ▹η    : id {Γ ▹ A} ≈ p ⁺ ∘ ⟨ q ⟩

    ∘ₑ = λ Γ Δ Θ γ δ → _∘_ {Δ} {Γ} {Θ} γ δ

    []Tₑ = λ Γ Δ n A γ → _[_]T {Γ} {Δ} {n} A γ

    []tₑ = λ Γ Δ n A a γ → _[_]t {Γ = Γ} {n} {A = A} {Δ = Δ} a γ

    ⟨⟩ₑ = λ Γ n A a → ⟨_⟩ {Γ} {n} {A} a

    ⁺ₑ = λ Γ Δ n A γ → _⁺ {Δ} {Γ} {n} {A} γ

    pₑ = λ Γ n A → p {Γ} {n} {A}

    qₑ = λ Γ n A → q {Γ} {n} {A}

    weave : {γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ} → γ ∘ δ ≈ γ' ∘ δ' → A [ γ ]T [ δ ]T ≈ A [ γ' ]T [ δ' ]T
    weave e = sym [∘]T ∙ cong (_ [_]T) $ e ∙ [∘]T
    -- Name inspired by 1Lab

    annihilate : γ ∘ δ ≈ id → A [ γ ]T [ δ ]T ≈ A
    annihilate e = sym [∘]T ∙ cong (_ [_]T) $ e ∙ [id]T
    -- Name inspired by 1Lab

    weave-t : {γ : Sub Ξ Γ}{δ : Sub Θ Ξ}{γ' : Sub Δ Γ}{δ' : Sub Θ Δ}
            → (e : γ ∘ δ ≈ γ' ∘ δ') → a [ γ ]t [ δ ]t ~[ cong (Tm _) $ weave e ] a [ γ' ]t [ δ' ]t
    weave-t e = sym [∘]t ∙ cong []tₑ $ refl $ refl $ refl $ refl $ refl $ e ∙ [∘]t

    annihilate-t : (e : γ ∘ δ ≈ id) → a [ γ ]t [ δ ]t ~[ cong (Tm _) $ annihilate e ] a
    annihilate-t e = sym [∘]t ∙ cong []tₑ $ refl $ refl $ refl $ refl $ refl $ e ∙ [id]t

    instance
      [p][⟨⟩]T : A [ p ]T [ ⟨ a ⟩ ]T ≈ A
      [p][⟨⟩]T = annihilate p∘⟨⟩

      [p][⟨⟩]t : a [ p ]t [ ⟨ b ⟩ ]t ~[ cong (Tm Δ) $ [p][⟨⟩]T ] a
      [p][⟨⟩]t = annihilate-t p∘⟨⟩

      [p][⁺]T : A [ p ]T [ γ ⁺ ]T ~[ cong (Ty (Δ ▹ A [ γ ]T) n) ] A [ γ ]T [ p ]T
      [p][⁺]T = weave p∘⁺

      [p][⁺]t : a [ p ]t [ γ ⁺ ]t ~[ cong (Tm (Δ ▹ A [ γ ]T)) $ [p][⁺]T ] a [ γ ]t [ p ]t
      [p][⁺]t = weave-t p∘⁺

      [▹η]T : A ≈ A [ p ⁺ ]T [ ⟨ q ⟩ ]T
      [▹η]T = sym (annihilate (sym ▹η))

      [▹η]t : a ~[ cong (Tm _) $ [▹η]T ] a [ p ⁺ ]t [ ⟨ q ⟩ ]t
      [▹η]t = sym (annihilate-t (sym ▹η))

      [⟨⟩][]T : A [ ⟨ a ⟩ ]T [ γ ]T ≈ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
      [⟨⟩][]T = weave ⟨⟩∘

      [⟨⟩][]t : a [ ⟨ b ⟩ ]t [ γ ]t ~[ cong (Tm _) $ [⟨⟩][]T ] a [ γ ⁺ ]t [ ⟨ b [ γ ]t ⟩ ]t
      [⟨⟩][]t = weave-t ⟨⟩∘

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c : Tm Γ A

  record LiftT : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      Lift     : Ty Γ n → Ty Γ (suc n)
      lift     : Tm Γ A → Tm Γ (Lift A)
      unlift   : Tm Γ (Lift A) → Tm Γ A
      Liftβ    : unlift (lift a) ≈ a
      Liftη    : lift (unlift a) ≈ a
      Lift[]   : (Lift A [ γ ]T) ≈ Lift (A [ γ ]T)
      lift[]   : lift a [ γ ]t ~[ cong (Tm _) $ Lift[] ] lift (a [ γ ]t)

    unlift[] : (unlift a) [ γ ]t ≈ unlift (coe (cong (Tm _) $ Lift[]) (a [ γ ]t))
    unlift[] {a} {γ} = sym Liftβ ∙ cong unlift $ (sym lift[] ∙ cong _[ γ ]t $ Liftη ∙ coh)

    liftₑ = λ Γ n A t → lift {Γ} {n} {A} t

    unliftₑ = λ Γ n A t → unlift {Γ} {n} {A} t

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c : Tm Γ A

  record UT : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      U    : (n : ℕ) → Ty Γ (suc n)
      El   : Tm Γ (U n) → Ty Γ n
      cd   : Ty Γ n → Tm Γ (U n)
      Uβ   : El (cd A) ≈ A
      Uη   : cd (El a) ≈ a
      U[]  : (U n) [ γ ]T ≈ U n
      cd[] : cd A [ γ ]t ~[ cong (Tm _) $ U[] ] cd (A [ γ ]T)

    El[] : El a [ γ ]T ≈ El (coe (cong (Tm _) $ U[]) (a [ γ ]t))
    El[] {a} {γ} = sym Uβ ∙ cong El $ (sym cd[] ∙ cong _[ γ ]t $ Uη ∙ coh)
  
module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c d f : Tm Γ A

  record Pi : Set (i ⊔ j ⊔ k ⊔ l) where
    infixl 9 _[_]Π
    field
      Π            : (A : Ty Γ n)(B : Ty (Γ ▹ A) n) → Ty Γ n
      instance Π[] : Π A B [ γ ]T ≈ Π (A [ γ ]T) (B [ γ ⁺ ]T)

    Πₑ = λ Γ n A B → Π {Γ} {n} A B
    
    _[_]Π : (f : Tm Γ (Π A B))(γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
    f [ γ ]Π = coe (cong (Tm _) $ Π[]) (f [ γ ]t)
    
    instance
      []Π   : a [ γ ]t ~[ cong (Tm _) $ Π[] ] a [ γ ]Π
      []Π = coh

    field
      lam            : (t : Tm (Γ ▹ A) B) → Tm Γ (Π A B)
      app            : (f : Tm Γ (Π A B))(a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
      instance Πβ    : app (lam b) a ≈ b [ ⟨ a ⟩ ]t
      instance Πη    : lam (app (f [ p ]Π) q) ~[ cong (Tm _) $ (cong (Π _) $ sym [▹η]T) ] f
      instance lam[] : lam b [ γ ]t ~[ cong (Tm _) $ Π[] ] lam (b [ γ ⁺ ]t)
    
    lamₑ = λ Γ n A B t → lam {Γ} {n} {A} {B} t
    
    appₑ = λ Γ n A B f a → app {Γ} {n} {A} {B} f a

    app' : Tm Γ (Π A B) → Tm (Γ ▹ A) B
    app' {(Γ)} {(n)} {(A)} {(B)} t = coe (cong (Tm (Γ ▹ A)) $ sym [▹η]T) (app (t [ p ]Π) q)

    app'ₑ = λ Γ n A B t → app' {Γ} {n} {A} {B} t

    app'β : app' (lam b) ≈ b
    app'β = sym coh ∙ cong appₑ $ refl $ refl $ refl $ refl $ (sym []Π ∙ lam[]) $ refl ∙ Πβ ∙ sym [▹η]t

    app'η : lam (app' b) ≈ b
    app'η = cong lamₑ $ refl $ refl $ refl $ [▹η]T $ sym coh ∙ Πη

    app'[] : app' b [ γ ⁺ ]t ≈ app' (b [ γ ]Π)
    app'[] {(Γ)} {(n)} {(A)} {(B)} {(b)} {(Δ)} {(γ)} = sym app'β
           ∙ sym coh
           ∙ cong appₑ
               $ refl
               $ refl
               $ refl
               $ refl
               $ (cong _[ p ]Π $ (sym lam[] ∙ cong _[ γ ]t $ app'η ∙ []Π))
               $ refl
           ∙ coh

    app'≈app : app' b [ ⟨ a ⟩ ]t ≈ app b a
    app'≈app = cong []tₑ $ refl $ refl $ refl $ [▹η]T $ sym coh $ refl ∙ sym Πβ ∙ cong appₑ $ refl $ refl $ refl $ sym [▹η]T $ Πη $ refl

    app[] : app f a [ γ ]t ~[ cong (Tm _) $ [⟨⟩][]T ] app (f [ γ ]Π) (a [ γ ]t)
    app[] {(Γ)} {(n)} {(A)} {(B)} {(f)} {(a)} {(Δ)} {(γ)} =
            cong []tₑ $ refl $ refl $ refl $ refl $ sym app'≈app $ refl
          ∙ [⟨⟩][]t
          ∙ cong []tₑ $ refl $ refl $ refl $ refl $ app'[] $ refl
          ∙ app'≈app

module _ {i j k l}(𝕊 : Sorts i j k l)(ℂ : CwF 𝕊) where
  open Sorts 𝕊
  open CwF ℂ

  private variable
    n m : ℕ
    Γ Δ Θ Ξ Ω : Con
    γ δ θ ξ : Sub Δ Γ
    A B C : Ty Γ n
    a b c d f : Tm Γ A

  record BoolT : Set (i ⊔ j ⊔ k ⊔ l) where
    field
      Bool             : Ty Γ 0
      instance Bool[]  : Bool [ γ ]T ≈ Bool
      true             : Tm Γ Bool
      false            : Tm Γ Bool
      instance true[]  : true [ γ ]t ~[ cong (Tm _) $ Bool[] ] true
      instance false[] : false [ γ ]t ~[ cong (Tm _) $ Bool[] ] false
      elim             : (A : Ty (Γ ▹ Bool) n) → Tm Γ (A [ ⟨ true ⟩ ]T) → Tm Γ (A [ ⟨ false ⟩ ]T) → (b : Tm Γ Bool) → Tm Γ (A [ ⟨ b ⟩ ]T)
      instance
        elim[]  :
          {A : Ty (Γ ▹ Bool) n} →
          {a : Tm Γ (A [ ⟨ true ⟩ ]T)} {b : Tm Γ (A [ ⟨ false ⟩ ]T)} →
          {c : Tm Γ Bool} {γ : Sub Δ Γ} →
          elim A a b c [ γ ]t
            ~[ cong (Tm _) $ weave (⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _ _) $ Bool[] $ coh)) ]
          elim
            (A [ coe (cong Sub $ (cong (_ ▹_) $ Bool[]) $ refl) (γ ⁺) ]T)
            (coe
              (cong (Tm _)
                $ weave (⟨⟩∘ ∙
                         (cong (∘ₑ _)
                            $ (cong (_ ▹_) $ Bool[]) $ refl
                            $ coh $ (cong (⟨⟩ₑ _ _) $ Bool[] $ true[]))))
              (a [ γ ]t))
            (coe
              (cong (Tm _)
                $ weave (⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _ _) $ Bool[] $ false[])) )
              (b [ γ ]t))
            (coe (cong (Tm _) $ Bool[]) (c [ γ ]t))
      instance Boolβ₁  : elim A a b true ≈ a
      instance Boolβ₂  : elim A a b false ≈ b
    elimₑ = λ Γ n A a b c → elim {Γ} {n} A a b c

record Model {i}{j}{k} : Set (lsuc (i ⊔ j ⊔ k)) where
  field
    instance sorts : Sorts i j k j
    instance cwf   : CwF sorts
    instance liftT : LiftT sorts cwf
    instance u     : UT sorts cwf
    instance pi    : Pi sorts cwf
    instance bool  : BoolT sorts cwf

  open Sorts sorts public
  open CwF cwf public
  open LiftT liftT public
  open UT u public
  open Pi pi public
  open BoolT bool public

open Model public
