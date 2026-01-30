module MLTT.Prelude where

private variable
  A A₀ A₁ : Set
  a a₀ a₁ a₂ : A

infix 4 _↝_
postulate
  _↝_ : A → A → Prop
{-# BUILTIN REWRITE _↝_ #-}

infix 4 _≡_
data _≡_ (a : A) : A → Prop where
  reflᴾ : a ≡ a

postulate
  coe₀ : A₀ ≡ A₁ → A₀ → A₁
  coe₀-refl : coe₀ reflᴾ a ↝ a
  {-# REWRITE coe₀-refl #-}

opaque
  coe : A₀ ≡ A₁ → A₀ → A₁
  coe = coe₀

infix 4 _≡[_]_
data _≡[_]_ (a₀ : A₀) (A₀₁ : A₀ ≡ A₁) (a₁ : A₁) : Prop where
  mkᴰ : coe A₀₁ a₀ ≡ a₁ → a₀ ≡[ A₀₁ ] a₁

pattern reflᴰ = mkᴰ reflᴾ

infix 4 _≅_
data _≅_ (a₀ : A₀) (a₁ : A₁) : Prop where
  mkᴴ : ∀ {A₀₁} → a₀ ≡[ A₀₁ ] a₁ → a₀ ≅ a₁

pattern reflᴴ = mkᴴ {A₀₁ = reflᴾ} reflᴰ

opaque
  unfolding coe

  type-eq : {a₀ : A₀} {a₁ : A₁} → a₀ ≅ a₁ → A₀ ≡ A₁
  type-eq reflᴴ = reflᴾ

  infix 0 by:_
  by:_ : a₀ ≅ a₁ → a₀ ≡ a₁
  by: reflᴴ = reflᴾ

  infix 0 byᴰ:_
  byᴰ:_ : (a₀₁ : a₀ ≅ a₁) → a₀ ≡[ type-eq a₀₁ ] a₁
  byᴰ: reflᴴ = reflᴰ

  ⌜_⌝ : a₀ ≡ a₁ → a₀ ≅ a₁
  ⌜ reflᴾ ⌝ = reflᴴ

  ⌜_⌝ᴰ : ∀ {A₀₁} → a₀ ≡[ A₀₁ ] a₁ → a₀ ≅ a₁
  ⌜_⌝ᴰ {A₀₁ = reflᴾ} reflᴰ = reflᴴ

  ap : (a : A) → a ≅ a
  ap a = reflᴴ

  refl : a ≅ a
  refl = reflᴴ

  sym : a₀ ≅ a₁ → a₁ ≅ a₀
  sym reflᴴ = reflᴴ

  infixr 9 _∙_
  _∙_ : a₀ ≅ a₁ → a₁ ≅ a₂ → a₀ ≅ a₂
  reflᴴ ∙ reflᴴ = reflᴴ

  wrap : {A₀₁ : A₀ ≡ A₁} → a₀ ≅ coe A₀₁ a₀
  wrap {A₀₁ = reflᴾ} = reflᴴ

  unwrap : {A₀₁ : A₀ ≡ A₁} → coe A₀₁ a₀ ≅ a₀
  unwrap {A₀₁ = reflᴾ} = reflᴴ

infixl 9 _▸_ _▸[_,_]_
infixr 0 Π-ext_ Πᵢ-ext_ Π-extᴴ_
postulate
  _▸_ :
    {B₀ : A₀ → Set} {B₁ : A₁ → Set} {f₀ : ∀ a₀ → B₀ a₀} {f₁ : ∀ a₁ → B₁ a₁} →
    f₀ ≅ f₁ → a₀ ≅ a₁ → f₀ a₀ ≅ f₁ a₁
  _▸[_,_]_ : -- maybe not needed
    {B₀ : A₀ → Set} {B₁ : A₁ → Set} {f₀ : ∀ a₀ → B₀ a₀} {f₁ : ∀ a₁ → B₁ a₁} →
    f₀ ≅ f₁ → ∀ a₀ a₁ → a₀ ≅ a₁ → f₀ a₀ ≅ f₁ a₁
  Π-ext_ :
    {B₀ : A → Set} {B₁ : A → Set} {f₀ : ∀ a → B₀ a} {f₁ : ∀ a → B₁ a} →
    (∀ a → f₀ a ≅ f₁ a) → f₀ ≅ f₁
  Πᵢ-ext_ :
    {B₀ : A → Set} {B₁ : A → Set} {f₀ : ∀ {a} → B₀ a} {f₁ : ∀ {a} → B₁ a} →
    (∀ {a} → f₀ {a} ≅ f₁ {a}) → (λ {a} → f₀ {a}) ≅ (λ {a} → f₁ {a})
  Π-extᴴ_ :
    {B₀ : A₀ → Set} {B₁ : A₁ → Set} {f₀ : ∀ a₀ → B₀ a₀} {f₁ : ∀ a₁ → B₁ a₁} →
    (∀ {a₀ a₁} → a₀ ≅ a₁ → f₀ a₀ ≅ f₁ a₁) → f₀ ≅ f₁

module M where
  Π : (A : Set) → (A → Set) → Set
  Π A B = (a : A) → B a

  postulate
    Π-inj₁ : {B₀ : A₀ → Set} {B₁ : A₁ → Set} → Π A₀ B₀ ≅ Π A₁ B₁ → A₀ ≅ A₁
    Π-inj₂ : {B₀ : A₀ → Set} {B₁ : A₁ → Set} → Π A₀ B₀ ≅ Π A₁ B₁ → B₀ ≅ B₁
    coe-Π :
      {B₀ : A₀ → Set} {B₁ : A₁ → Set} {e : Π A₀ B₀ ≡ Π A₁ B₁} {f₀ : Π A₀ B₀} →
      coe e f₀ ↝
      λ a₁ →
      coe (by: Π-inj₂ ⌜ e ⌝ ▸ unwrap) (f₀ (coe (by: sym (Π-inj₁ ⌜ e ⌝)) a₁))
    {-# REWRITE coe-Π #-}

  record ⊤ : Set where
    constructor tt

  infixl 4 _,_
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst

  open Σ public

  ,ₑ = λ A B a b → _,_ {A} {B} a b

  postulate
    Σ-inj₁ : {B₀ : A₀ → Set} {B₁ : A₁ → Set} → Σ A₀ B₀ ≅ Σ A₁ B₁ → A₀ ≅ A₁
    Σ-inj₂ : {B₀ : A₀ → Set} {B₁ : A₁ → Set} → Σ A₀ B₀ ≅ Σ A₁ B₁ → B₀ ≅ B₁
    coe-Σ :
      {B₀ : A₀ → Set} {B₁ : A₁ → Set} {e : Σ A₀ B₀ ≡ Σ A₁ B₁} {t₀ : Σ A₀ B₀} →
      coe e t₀ ↝ (coe (by: Σ-inj₁ ⌜ e ⌝) (t₀ .fst) , coe (by: Σ-inj₂ ⌜ e ⌝ ▸ {!!}) (t₀ .snd))

---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}
