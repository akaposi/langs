{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)

module mltt-minimal.Syntax where

the : ∀{i}(A : Set i) → A → A
the _ x = x

infixl 5 _▹_
infixl 8 _∘_ _∘'_ _∘*_
infixl 9 _[_]T _[_]T' _[_]t _[_]t' _[_]T* _[_]t* _[_]U _[_]U' _[_]T= _[_]t=
infixl 10 _⁺ _⁺' _⁺*

data Con : Type
data Sub : Con → Con → Type
data Ty  : Con → Type
data Tm  : (Γ : Con) → Ty Γ → Type

private variable
  Γ Δ Θ Ξ : Con
  γ δ θ ξ σ γa : Sub Δ Γ
  A B C : Ty Γ
  a b c Â t : Tm Γ A

data Con where
  _▹_ : (Γ : Con) → Ty Γ → Con
  ◇   : Con

_∘'_   : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
id'    : Sub Γ Γ

_[_]T'    : Ty Γ → Sub Δ Γ → Ty Δ

p'     : Sub (Γ ▹ A) Γ
⟨_⟩'   : Tm Γ A → Sub Γ (Γ ▹ A)
_⁺'    : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T') (Γ ▹ A)
_[_]t' : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T')
U'     : Ty Γ
_[_]U' : Tm Γ U' → (γ : Sub Δ Γ) → Tm Δ U'
q'     : Tm (Γ ▹ A) (A [ p' ]T')

data Ty where
  TySet      : isSet (Ty Γ)
  _[_]T      : Ty Γ → Sub Δ Γ → Ty Δ
  [∘]T       : A [ γ ∘' δ ]T ≡ A [ γ ]T [ δ ]T
  [id]T      : A [ id' ]T ≡ A
  [p][⟨⟩]T   : {A : Ty Γ}{b : Tm Γ B} → A [ p' ]T [ ⟨ b ⟩' ]T ≡ A
  [p][⁺]T    : A [ p' {A = B} ]T [ γ ⁺' ]T ≡ A [ γ ]T [ p' ]T
  [p⁺][⟨q⟩]T : A ≡ A [ p' ⁺' ]T [ ⟨ q' ⟩' ]T
  [⟨⟩][]T    : A [ ⟨ a ⟩' ]T [ γ ]T ≡ A [ γ ⁺' ]T [ ⟨ a [ γ ]t' ⟩' ]T

  
  U        : Ty Γ
  U[]      : U [ γ ]T ≡ U
  El       : Tm Γ U' → Ty Γ
  El[]     : El Â [ γ ]T ≡ El (Â [ γ ]U')
  
  Π        : (A : Ty Γ) → Ty (Γ ▹ A) → Ty Γ
  Π[]      : Π A B [ γ ]T ≡ Π (A [ γ ]T') (B [ γ ⁺' ]T)

_[_]T' = _[_]T
U'      = U

data Sub where
  SubSet : isSet (Sub Δ Γ)
  _∘_    : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  ass    : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
  id     : Sub Γ Γ
  idl    : id ∘ γ ≡ γ
  idr    : γ ∘ id ≡ γ
  ε      : Sub Γ ◇
  ◇η     : σ ≡ ε
  p      : Sub (Γ ▹ A) Γ
  _⁺     : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
  ⟨_⟩    : Tm Γ A → Sub Γ (Γ ▹ A)
  ∘⁺     : PathP (λ i → Sub (Θ ▹ [∘]T {A = A}{γ = γ}{δ = δ} i) (Γ ▹ A)) ((γ ∘' δ) ⁺) (γ ⁺ ∘' δ ⁺)
  id⁺    : PathP (λ i → Sub (Γ ▹ [id]T {A = A} i) (Γ ▹ A)) (id' ⁺) id'
  p∘⁺    : p {A = A} ∘ γ ⁺ ≡ γ ∘ p
  p∘⟨⟩   : p ∘ ⟨ a ⟩ ≡ id
  ⟨⟩∘    : ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]t' ⟩
  p⁺∘⟨q⟩ : p' ⁺ ∘ ⟨ q' ⟩ ≡ id {Γ ▹ A}

_∘'_ = _∘_
id'  = id
p'   = p
⟨_⟩' = ⟨_⟩
_⁺'  = _⁺

data Tm where
  TmSet : isSet (Tm Γ A)
  _[_]t : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
  q     : Tm (Γ ▹ A) (A [ p ]T)
  q[⟨⟩] : PathP (λ i → Tm Γ ([p][⟨⟩]T {A = A}{b = a} i)) (q [ ⟨ a ⟩ ]t) a
  q[⁺]  : PathP (λ i → Tm (Δ ▹ A [ γ ]T) ([p][⁺]T {A = A} i)) (q [ γ ⁺ ]t) q
  [∘]t  : PathP (λ i → Tm Θ ([∘]T {A = A}{γ = γ}{δ = δ} i)) (a [ γ ∘ δ ]t) (a [ γ ]t [ δ ]t)
  [id]t : PathP (λ i → Tm Γ ([id]T {A = A} i)) (a [ id ]t) a

  _[_]U : Tm Γ U → (γ : Sub Δ Γ) → Tm Δ U
  []U   : PathP (λ i → Tm Δ (U[] {γ = γ} i)) (Â [ γ ]t) (Â [ γ ]U)

  _[_]Π : Tm Γ (Π A B) → (γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
  lam   : Tm (Γ ▹ A) B → Tm Γ (Π A B)
  app   : Tm Γ (Π A B) → (a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
  Πβ    : app (lam b) a ≡ b [ ⟨ a ⟩ ]t
  Πη    : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Γ (Π A ([p⁺][⟨q⟩]T {A = B} i))) t (lam (app (t [ p ]Π) q'))
  lam[] : PathP (λ i → Tm Γ (Π[] {B = B}{γ = γ} i)) (lam b [ γ ]t) (lam (b [ γ ⁺ ]t))
  app[] : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Γ ([⟨⟩][]T {A = B}{a = a}{γ = γ} i)) (app t a [ γ ]t') (app (t [ γ ]Π) (a [ γ ]t'))

_[_]t' = _[_]t
q'     = q
_[_]U' = _[_]U

_[_]T* : Ty Γ → Sub Δ Γ → Ty Δ
_[_]T= : (A : Ty Γ)(γ : Sub Δ Γ) → A [ γ ]T ≡ A [ γ ]T*
_[_]t* : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T*)
_[_]t= : (a : Tm Γ A)(γ : Sub Δ Γ) → PathP (λ i → Tm Δ ((A [ γ ]T=) i)) (a [ γ ]t) (a [ γ ]t*)
_∘*_   : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
_∘=_   : (γ : Sub Δ Γ)(δ : Sub Θ Δ) → γ ∘ δ ≡ γ ∘* δ

_⁺*    : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T*) (Γ ▹ A)
_⁺* {Δ = Δ}{Γ = Γ}{A = A} γ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) (A [ γ ]T=) (γ ⁺)

∘-substᵣ : {Γ Δ : Con}{γ : Sub Δ Γ}{Θ Θ' : Con}{δ : Sub Θ Δ}{e : Θ ≡ Θ'} → γ ∘ subst (λ z → Sub z Δ) e δ ≡ subst (λ z → Sub z Γ) e (γ ∘ δ)
∘-substᵣ {Γ} {Δ} {γ} {Θ} {Θ'} {δ} {e} = J {x = Θ} (λ a eq → γ ∘ subst (λ z → Sub z Δ) eq δ ≡ subst (λ z → Sub z Γ) eq (γ ∘ δ)) (cong (γ ∘_) (substRefl {B = λ z → Sub z Δ} δ) ∙ sym (substRefl {B = λ z → Sub z Γ} (γ ∘ δ))) e

∘-substₘ : {Γ Δ : Con}{γ : Sub Δ Γ}{Θ Δ' : Con}{δ : Sub Θ Δ'}{e : Δ ≡ Δ'} → γ ∘ subst (λ z → Sub Θ z) (sym e) δ ≡ subst (λ z → Sub z Γ) e γ ∘ δ
∘-substₘ {Γ} {Δ} {γ} {Θ} {Δ'} {δ} {e} = J (λ a eq → ∀ δ → γ ∘ subst (λ z → Sub Θ z) (sym eq) δ ≡ subst (λ z → Sub z Γ) eq γ ∘ δ) (λ δ' → congS (γ ∘_) (transportRefl δ') ∙ congS (_∘ δ') (sym (transportRefl γ))) e δ

∘-substₗ : {Γ Δ : Con}{γ : Sub Δ Γ}{Θ Γ' : Con}{δ : Sub Θ Δ}{e : Γ ≡ Γ'} → subst (λ z → Sub Δ z) e γ ∘ δ ≡ subst (λ z → Sub Θ z) e (γ ∘ δ)
∘-substₗ {Γ} {Δ} {γ} {Θ} {Γ'} {δ} {e} = J (λ a eq → subst (λ z → Sub Δ z) eq γ ∘ δ ≡ subst (λ z → Sub Θ z) eq (γ ∘ δ)) (congS (_∘ δ) (substRefl {B = λ z → Sub z Γ} γ) ∙ sym (substRefl {B = λ z → Sub Θ z} (γ ∘ δ))) e

subst-p : {Γ : Con}{A B : Ty Γ}{e : A ≡ B} → subst (λ z → Sub (Γ ▹ z) Γ) e p ≡ p
subst-p {Γ} {A} {B} {e} = J (λ _ eq → subst (λ z → Sub (Γ ▹ z) Γ) eq p ≡ p) (transportRefl p) e

subst-cong-p : {Γ : Con}{A B : Ty Γ}{e : A ≡ B} → subst (λ z → Sub z Γ) (congS (Γ ▹_) e) p ≡ p
subst-cong-p {Γ} {A} {B} {e} = subst-p {Γ} {A} {B} {e}

TySet A A' e e' i i' [ γ ]T* = TySet (A [ γ ]T*) (A' [ γ ]T*) (λ i → e i [ γ ]T*) (λ i → e' i [ γ ]T*) i i'
(A [ γ ]T) [ δ ]T* = A [ γ ∘* δ ]T
_[_]T* {Γ} {Δ} ([∘]T {Θ} {A} {Ψ} {θ} {_} {ψ} i) γ = (A [ θ ]T [ ψ ∘* γ ]T=) (~ i) -- [∘]T {Θ} {A} {Ψ} {θ} {_} {ψ} i [ γ ]T
_[_]T* {Γ} {Δ} ([id]T {_} {A} i) γ = (A [ γ ]T=) i
_[_]T* {Γ} {Δ} ([p][⟨⟩]T {_} {A} {B} {t} i) γ = [p][⟨⟩]T-helper i where
  [p][⟨⟩]T-helper : B [ p {_} {A} ]T [ γ ⁺* ∘ ⟨ t [ γ ]t* ⟩ ]T ≡ B [ γ ]T*
  [p][⟨⟩]T-helper = [∘]T {A = B [ p ]T} {γ = γ ⁺*}
                  ∙ congS (_[ ⟨ t [ γ ]t* ⟩ ]T) ( sym ([∘]T {A = B} {γ = p})
                                                ∙ congS (B [_]T) ( ∘-substᵣ {γ = p} {δ = γ ⁺} {congS (Δ ▹_) (A [ γ ]T=)}
                                                                 ∙ congS (subst (λ z → Sub z Γ) (λ i₁ → Δ ▹ (A [ γ ]T=) i₁)) p∘⁺
                                                                 ∙ sym (∘-substᵣ {γ = γ} {δ = p} {congS (Δ ▹_) (A [ γ ]T=)})
                                                                 ∙ congS (γ ∘_) (subst-p {e = A [ γ ]T=})
                                                                 )
                                                ∙ [∘]T
                                                )
                  ∙ [p][⟨⟩]T {A = B [ γ ]T}
                  ∙ (B [ γ ]T=)

_[_]T* {_} {Δ} ([p][⁺]T {Θ} {A} {B} {Γ} {θ} i) γ = ([∘]T ∙ congS _[ γ ]T ([p][⁺]T {Θ} {A} {B} {Γ} {θ}) ∙ sym [∘]T) i
_[_]T* {_} {Δ} ([p⁺][⟨q⟩]T {Γ} {A} {B} i) γ = [p⁺][⟨q⟩]T-helper (~ i) where
  [p⁺][⟨q⟩]T-helper : B [ p' ⁺' ]T [ γ ⁺* ∘ ⟨ q' [ γ ]t* ⟩ ]T ≡ B [ γ ]T*
  [p⁺][⟨q⟩]T-helper = {!!}
  -- congS (λ x → _[_]T {Γ = Γ ▹ A ▹ A [ p ]T} {Δ = Δ} (_[_]T {Γ = Γ ▹ A} {Δ = Γ ▹ A ▹ A [ p ]T} B (_⁺ {Δ = Γ ▹ A} {Γ = Γ} {A = A} (p {Γ = Γ} {A = A}))) x) {!!} ∙ {!!}

_[_]T* {Γ} {Δ} ([⟨⟩][]T {Θ} {A} {B} {t} {_} {δ} i) γ = {!!}
U [ γ ]T* = U
_[_]T* {Γ} {Δ} (U[] {_} {Θ} {θ} i) γ = U[] {Δ} {Θ} {θ ∘* γ} i
El Â [ γ ]T* = El (Â [ γ ]t*)
_[_]T* {Γ} {Δ} (El[] {Θ} {Â} {_} {θ} i) γ = {!!}
Π A B [ γ ]T* = Π (A [ γ ]T*) (B [ γ ⁺* ]T*)
Π[] i [ γ ]T* = {!!}

{-
hcomp (λ l → λ { (i = i0) → {!!}
                                                 ; (i = i1) → {!!}
                                                 ; (j = i0) → {!!}
                                                 ; (j = i1) → {!!}
                                                 ; (k = i0) → TySet A A' e e' i j [ γ ]T
                                                 ; (k = i1) → {!!}}) {!!}
-}

TySet A A' e e' i j [ γ ]T= = {!!}
A [ γ ]T [ δ ]T= = {!!}
[∘]T i [ γ ]T= = {!!}
[id]T i [ γ ]T= = {!!}
[p][⟨⟩]T i [ γ ]T= = {!!}
[p][⁺]T i [ γ ]T= = {!!}
[p⁺][⟨q⟩]T i [ γ ]T= = {!!}
[⟨⟩][]T i [ γ ]T= = {!!}
U [ γ ]T= = {!!}
U[] i [ γ ]T= = {!!}
El t [ γ ]T= = {!!}
El[] i [ γ ]T= = {!!}
Π A B [ γ ]T= = {!!}
Π[] i [ γ ]T= = {!!}

SubSet γ γ₁ e₁ e₂ i j ∘* δ = SubSet (γ ∘* δ) (γ₁ ∘* δ) (λ i → e₁ i ∘* δ) (λ i → e₂ i ∘* δ) i j 
γ ∘ δ ∘* θ = γ ∘* (δ ∘* θ)
ass {γ = γ} {δ = δ} {θ = θ} i ∘* Ξ = γ ∘* (δ ∘* (θ ∘* Ξ))
id ∘* δ = δ
idl {Γ} {Δ} {γ} i ∘* δ = γ ∘* δ
idr {Γ} {Δ} {γ} i ∘* δ = γ ∘* δ
ε ∘* δ = ε
◇η {σ = σ} i ∘* δ = ◇η {σ = σ ∘* δ} i
p ∘* δ = p ∘ δ
γ ⁺ ∘* δ = γ ⁺ ∘ δ
⟨ a ⟩ ∘* γ = γ ⁺* ∘ ⟨ a [ γ ]t* ⟩
_∘*_ {_} {_} {Θ} (∘⁺ {Δ} {Γ} {A} {Ξ} {γ} {ξ} i) = ∘⁺-helper i where
  ∘⁺-helper : PathP (λ i → Sub Θ (Δ ▹ [∘]T {Γ} {A} {Ξ} {γ} {Δ} {ξ} i) → Sub Θ (Γ ▹ A)) (λ δ → (γ ∘' ξ) ⁺ ∘ δ) (λ δ → γ ⁺ ∘ (ξ ⁺ ∘ δ))
  ∘⁺-helper = toPathP (funExt λ δ → transportRefl ((γ ∘ ξ) ⁺ ∘ transport (λ i₁ → Sub Θ (Δ ▹ [∘]T {Γ} {A} {Ξ} {γ} {Δ} {ξ} (~ i₁))) δ)
                                  ∙ ∘-substₘ {γ = (γ ∘ ξ) ⁺} {δ = δ} {e = congS (Δ ▹_) [∘]T}
                                  ∙ congS (_∘ δ) (fromPathP ∘⁺)
                                  ∙ ass)

_∘*_ {_} {_} {Θ} (id⁺ {Δ} {A} i) = id⁺-helper i where
  id⁺-helper : PathP (λ i → Sub Θ (Δ ▹ [id]T {Δ} {A} i) → Sub Θ (Δ ▹ A)) (λ z → id' ⁺ ∘ z) (λ z → z)
  id⁺-helper = toPathP (funExt λ δ → transportRefl (id ⁺ ∘ (transport (λ i₁ → Sub Θ (Δ ▹ [id]T {_} {A} (~ i₁))) δ))
                                   ∙ ∘-substₘ {γ = id ⁺} {δ = δ} {e = congS (Δ ▹_) [id]T}
                                   ∙ congS (_∘ δ) (fromPathP id⁺)
                                   ∙ idl)

--   transport (λ i₁ → Sub Θ (Δ ▹ [id]T i₁) → Sub Θ (Δ ▹ A)) (λ z → id' ⁺ ∘ z) δ
-- ≝ transport refl (id ⁺ ∘ (transport (λ i₁ → Sub Θ (Δ ▹ [id]T (~ i₁))) δ))

-- _∘_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
-- id ⁺ : Sub (Δ ▹ A[id]) (Δ ▹ A)
-- id⁺ ∘_ : Sub Θ (Δ ▹ A[id]) → Sub Θ (Δ ▹ A)
--
-- transport refl ((id ⁺) ∘ transport (λ i₁ → Sub Θ (Δ) → Sub Θ (Δ)) (λ z → z))

{-
e : A → B ≡ C → D
e1 : A ≡ C
e2 : B ≡ D
f : A → B
c : C
(transport e f) c ∼> transport e2 (f (transport (sym e1) c))

(transport (λ i₁ → Sub Θ (Δ ▹ [id]T i₁) → Sub Θ (Δ ▹ A)) (λ z → id' ⁺ ∘ z)) δ ∼>

transport refl (id ⁺ ∘ (transport (λ i₁ → Sub Θ (Δ ▹ [id]T (~ i₁))) δ))

-}

-- compPathP -- id⁺ i ∘ δ
-- {A = ?} {B = ?} (λ j a → ? ∘ δ) {id ⁺} {id} id⁺ i
_∘*_ {_} {Γ} {Θ} (p∘⁺ {_} {A} {Δ} {γ} i) δ = p∘⁺-helper i where
  p∘⁺-helper : p ∘ (γ ⁺ ∘ δ) ≡ γ ∘* (p ∘ δ)
  p∘⁺-helper = sym ass
             ∙ congS (_∘ δ) p∘⁺
             ∙ ass
             ∙ (γ ∘= (p ∘ δ))

_∘*_ {Δ} {_} {Θ} (p∘⟨⟩ {_} {A} {t} i) δ = p∘⟨⟩-helper i where
  p∘⟨⟩-helper : _∘_ {Δ ▹ A} {Δ} {Θ} p (subst (λ z → Sub (Θ ▹ z) (Δ ▹ A)) (A [ δ ]T=) (δ ⁺) ∘ ⟨ t [ δ ]t* ⟩) ≡ δ
  p∘⟨⟩-helper = sym ass
              ∙ congS (_∘ ⟨ t [ δ ]t* ⟩) (∘-substᵣ {γ = p} {δ = δ ⁺} {e = congS (Θ ▹_) (A [ δ ]T=)})
              ∙ congS (λ x → subst (λ z → Sub z Δ) (λ i₁ → Θ ▹ (A [ δ ]T=) i₁) x ∘ ⟨ t [ δ ]t* ⟩) (p∘⁺ {γ = δ})
              ∙ congS (_∘ ⟨ t [ δ ]t* ⟩) (sym (∘-substᵣ {γ = δ} {δ = p} {e = congS (Θ ▹_) (A [ δ ]T=)}))
              ∙ ass
              ∙ congS (δ ∘_) (congS (_∘ ⟨ t [ δ ]t* ⟩) (subst-p {e = A [ δ ]T=})
                             ∙ p∘⟨⟩
                             )
              ∙ idr

_∘*_ {Δ} {_} {Θ} (⟨⟩∘ {Γ} {A} {t} {.Δ} {γ} i) δ = ⟨⟩∘-helper i where
  ⟨⟩∘-helper : (γ ∘* δ) ⁺* ∘ ⟨ t [ γ ∘* δ ]t* ⟩ ≡ γ ⁺ ∘ (δ ⁺* ∘ ⟨ t [ γ ]t' [ δ ]t* ⟩)
  ⟨⟩∘-helper = {!!}

_∘*_ {_} {_} {Θ} (p⁺∘⟨q⟩ {Δ} {A} i) δ = p⁺∘⟨q⟩-helper i where
  p⁺∘⟨q⟩-helper : p ⁺ ∘ (δ ⁺* ∘ ⟨ q [ δ ]t* ⟩) ≡ δ
  p⁺∘⟨q⟩-helper = {!!}

_∘=_ {Δ} {Γ} {Θ} γ δ = {!!}

a [ γ ]t* = {!!}

a [ γ ]t= = {!!}
