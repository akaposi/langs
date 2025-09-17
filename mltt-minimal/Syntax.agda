{-# OPTIONS --cubical #-}

module mltt-minimal.Syntax where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

infixl 5 _▹_
infixl 8 _∘_
infixl 9 _[_]T _[_]t _[_]U _[_]Π
infixl 10 _⁺
infixl 11 ⟨_⟩

-- Szumi's method

data Sort : Type
data EL : Sort → Type

Con : Type
Sub : Con → Con → Type
Ty : Con → Type
Tm : (Γ : Con) → Ty Γ → Type

data Sort where
  con : Sort
  sub : (Δ Γ : Con) → Sort
  ty : (Γ : Con) → Sort
  tm : (Γ : Con)(A : Ty Γ) → Sort

Con = EL con
Sub Δ Γ = EL (sub Δ Γ)
Ty Γ = EL (ty Γ)
Tm Γ A = EL (tm Γ A)

{-# DISPLAY EL con = Con #-}
{-# DISPLAY EL (sub Δ Γ) = Sub Δ Γ #-}
{-# DISPLAY EL (ty Γ) = Ty Γ #-}
{-# DISPLAY EL (tm Γ A) = Tm Γ A #-}

private variable
  Γ Δ Θ : Con
  γ δ θ σ : Sub Δ Γ
  A B : Ty Γ
  a b Â t : Tm Γ A

data EL where
  SubSet : isSet (Sub Δ Γ)
  TySet  : isSet (Ty Γ)
  TmSet  : isSet (Tm Γ A)

  -- Con
  _▹_ : (Γ : Con)(A : Ty Γ) → Con
  ◇   : Con

  -- Sub
  _∘_    : (γ : Sub Δ Γ)(δ : Sub Θ Δ) → Sub Θ Γ
  ass    : (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
  id     : Sub Γ Γ
  idl    : id ∘ γ ≡ γ
  idr    : γ ∘ id ≡ γ
  ε      : Sub Γ ◇
  ◇η     : σ ≡ ε
  p      : Sub (Γ ▹ A) Γ
  ⟨_⟩    : (t : Tm Γ A) → Sub Γ (Γ ▹ A)
  p∘⟨⟩   : p ∘ ⟨ a ⟩ ≡ id

    -- Ty
  _[_]T    : (A : Ty Γ)(γ : Sub Δ Γ) → Ty Δ
  [∘]T     : A [ γ ∘ δ ]T ≡ A [ γ ]T [ δ ]T
  [id]T    : A [ id ]T ≡ A
  [p][⟨⟩]T : {A : Ty Γ}{b : Tm Γ B} → A [ p ]T [ ⟨ b ⟩ ]T ≡ A
  -- [p][⁺]T needs _⁺
  -- [p⁺][⟨q⟩]T and [⟨⟩][]T rules are lower, q and _[_]t are needed for these.
  U        : Ty Γ
  U[]      : U [ γ ]T ≡ U
  El       : (Â : Tm Γ U) → Ty Γ
  -- El[] is below Tm stuff
  Π        : (A : Ty Γ)(B : Ty (Γ ▹ A)) → Ty Γ
  -- Π[] needs _⁺

  -- Tm
  _[_]t : (t : Tm Γ A)(γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)
  q     : Tm (Γ ▹ A) (A [ p ]T)
  q[⟨⟩] : PathP (λ i → Tm Γ ([p][⟨⟩]T {A = A}{b = a} i)) (q [ ⟨ a ⟩ ]t) a
  [∘]t  : PathP (λ i → Tm Θ ([∘]T {A = A}{γ = γ}{δ = δ} i)) (a [ γ ∘ δ ]t) (a [ γ ]t [ δ ]t)
  [id]t : PathP (λ i → Tm Γ ([id]T {A = A} i)) (a [ id ]t) a

  _[_]U : (u : Tm Γ U)(γ : Sub Δ Γ) → Tm Δ U
  []U   : PathP (λ i → Tm Δ (U[] {γ = γ} i)) (Â [ γ ]t) (Â [ γ ]U)

  -- Sub again
  _⁺     : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T) (Γ ▹ A)
  ∘⁺     : PathP (λ i → Sub (Θ ▹ [∘]T {A = A}{γ = γ}{δ = δ} i) (Γ ▹ A)) ((γ ∘ δ) ⁺) (γ ⁺ ∘ δ ⁺)
  id⁺    : PathP (λ i → Sub (Γ ▹ [id]T {A = A} i) (Γ ▹ A)) (id ⁺) id
  p∘⁺    : p {A = A} ∘ γ ⁺ ≡ γ ∘ p
  ⟨⟩∘    : ⟨ a ⟩ ∘ γ ≡ γ ⁺ ∘ ⟨ a [ γ ]t ⟩
  p⁺∘⟨q⟩ : p ⁺ ∘ ⟨ q ⟩ ≡ id {Γ ▹ A}

    -- Ty again
  [p][⁺]T    : A [ p {A = B} ]T [ γ ⁺ ]T ≡ A [ γ ]T [ p ]T
  [p⁺][⟨q⟩]T : A [ p ⁺ ]T [ ⟨ q ⟩ ]T ≡ A
  [⟨⟩][]T    : A [ ⟨ a ⟩ ]T [ γ ]T ≡ A [ γ ⁺ ]T [ ⟨ a [ γ ]t ⟩ ]T
  El[]       : El Â [ γ ]T ≡ El (Â [ γ ]U)
  Π[]        : Π A B [ γ ]T ≡ Π (A [ γ ]T) (B [ γ ⁺ ]T)

  -- Tm again
  q[⁺]  : PathP (λ i → Tm (Δ ▹ A [ γ ]T) ([p][⁺]T {A = A} i)) (q [ γ ⁺ ]t) q

  _[_]Π : (f : Tm Γ (Π A B))(γ : Sub Δ Γ) → Tm Δ (Π (A [ γ ]T) (B [ γ ⁺ ]T))
  []Π   : PathP (λ i → Tm Δ (Π[] {A = A} {B = B} {γ = γ} i)) (t [ γ ]t) (t [ γ ]Π)
  lam   : (t : Tm (Γ ▹ A) B) → Tm Γ (Π A B)
  app   : (f : Tm Γ (Π A B))(a : Tm Γ A) → Tm Γ (B [ ⟨ a ⟩ ]T)
  Πβ    : app (lam b) a ≡ b [ ⟨ a ⟩ ]t
  Πη    : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Γ (Π A ([p⁺][⟨q⟩]T {A = B} i))) (lam (app (t [ p ]Π) q)) t
  lam[] : PathP (λ i → Tm Γ (Π[] {B = B}{γ = γ} i)) (lam b [ γ ]t) (lam (b [ γ ⁺ ]t))
  app[] : {t : Tm Γ (Π A B)} → PathP (λ i → Tm Δ ([⟨⟩][]T {A = B}{a = a}{γ = γ} i)) (app t a [ γ ]t) (app (t [ γ ]Π) (a [ γ ]t))

substd₂ : ∀{i j k}{A : Set i}{B : A → Set j}(P : (a : A) → B a → Set k){x x' : A}{y : B x}{y' : B x'}(e : x ≡ x') → PathP (λ i → B (e i)) y y' → P x y → P x' y'
substd₂ P e1 e2 pxy = transport (λ i → P (e1 i) (e2 i)) pxy
-- _◁_▷_
--

subst-∘ᵣ : {Γ Δ : Con}{γ : Sub Δ Γ}{Θ Θ' : Con}{δ : Sub Θ Δ}{e : Θ ≡ Θ'} → γ ∘ subst (λ z → Sub z Δ) e δ ≡ subst (λ z → Sub z Γ) e (γ ∘ δ)
subst-∘ᵣ {Γ} {Δ} {γ} {Θ} {Θ'} {δ} {e} = J {x = Θ} (λ _ eq → γ ∘ subst (λ z → Sub z Δ) eq δ ≡ subst (λ z → Sub z Γ) eq (γ ∘ δ)) (cong (γ ∘_) (substRefl {B = λ z → Sub z Δ} δ) ∙ sym (substRefl {B = λ z → Sub z Γ} (γ ∘ δ))) e

subst-∘ₘ : {Γ Δ : Con}{γ : Sub Δ Γ}{Θ Δ' : Con}{δ : Sub Θ Δ'}{e : Δ ≡ Δ'} → γ ∘ subst (λ z → Sub Θ z) (sym e) δ ≡ subst (λ z → Sub z Γ) e γ ∘ δ
subst-∘ₘ {Γ} {Δ} {γ} {Θ} {Δ'} {δ} {e} = J (λ _ eq → ∀ δ → γ ∘ subst (λ z → Sub Θ z) (sym eq) δ ≡ subst (λ z → Sub z Γ) eq γ ∘ δ) (λ δ' → congS (γ ∘_) (transportRefl δ') ∙ congS (_∘ δ') (sym (transportRefl γ))) e δ

subst-∘ₗ : {Γ Δ : Con}{γ : Sub Δ Γ}{Θ Γ' : Con}{δ : Sub Θ Δ}{e : Γ ≡ Γ'} → subst (λ z → Sub Δ z) e γ ∘ δ ≡ subst (λ z → Sub Θ z) e (γ ∘ δ)
subst-∘ₗ {Γ} {Δ} {γ} {Θ} {Γ'} {δ} {e} = J (λ _ eq → subst (λ z → Sub Δ z) eq γ ∘ δ ≡ subst (λ z → Sub Θ z) eq (γ ∘ δ)) (congS (_∘ δ) (substRefl {B = λ z → Sub z Γ} γ) ∙ sym (substRefl {B = λ z → Sub Θ z} (γ ∘ δ))) e

subst-p : {Γ : Con}{A B : Ty Γ}{e : A ≡ B} → subst (λ z → Sub (Γ ▹ z) Γ) e p ≡ p
subst-p {Γ} {A} {B} {e} = J (λ _ eq → subst (λ z → Sub (Γ ▹ z) Γ) eq p ≡ p) (transportRefl p) e

subst-cong-p : {Γ : Con}{A B : Ty Γ}{e : A ≡ B} → subst (λ z → Sub z Γ) (congS (Γ ▹_) e) p ≡ p
subst-cong-p {Γ} {A} {B} {e} = subst-p {Γ} {A} {B} {e}

subst-⟨⟩ : {t : Tm Δ A}{e : A ≡ B} → subst (λ z → Sub Δ (Δ ▹ z)) e ⟨ t ⟩ ≡ ⟨ subst (Tm Δ) e t ⟩
subst-⟨⟩ {Δ = Δ} {A = A} {B = B} {t} {e} = J (λ _ eq → subst (λ z → Sub Δ (Δ ▹ z)) eq ⟨ t ⟩ ≡ ⟨ subst (Tm Δ) eq t ⟩) (transportRefl ⟨ t ⟩ ∙ congS ⟨_⟩ (sym (transportRefl t))) e

subst-[]T : ∀{Γ Δ}{A : Ty Γ}{γ : Sub Δ Γ}{Δ'}{e : Δ ≡ Δ'} → subst Ty e (A [ γ ]T) ≡ A [ subst (λ z → Sub z Γ) e γ ]T
subst-[]T {Γ} {Δ} {A} {γ} {Δ'} {e} = J (λ _ eq → subst Ty eq (A [ γ ]T) ≡ A [ subst (λ z → Sub z Γ) eq γ ]T) (transportRefl (A [ γ ]T) ∙ congS (A [_]T) (sym (transportRefl γ))) e

-- (transport (λ i → Tm (e i) (transport (λ j → Ty (e (i ∧ j))) (A [ γ ]T))) {!t [ γ ]t!})
-- PathP (λ i → Tm (e i) (toPathP {A = λ i → Ty (e i)} {x = A [ γ ]T} (subst-[]T {A = A} {γ} {e = e}) i)) (t [ γ ]t) (t [ subst (λ z → Sub z Γ) e γ ]t)
-- (substd₂ Tm e (subst-filler Ty e (A [ γ ]T)) (t [ γ ]t))
subst-Sub-[]t : ∀{Γ Δ}{A : Ty Γ}{t : Tm Γ A}{γ : Sub Δ Γ}{Δ'}{e : Δ ≡ Δ'} → PathP (λ i → Tm Δ' (subst-[]T {A = A} {γ} {e = e} i)) (transport (λ i → Tm (e i) (subst-filler Ty e (A [ γ ]T) i)) (t [ γ ]t)) (t [ subst (λ z → Sub z Γ) e γ ]t)
subst-Sub-[]t {Γ} {Δ} {A} {t} {γ} {Δ'} {e} = J (λ Δ' e1 → PathP (λ i → Tm Δ' (subst-[]T {A = A} {γ} {e = e1} i)) (transport (λ i → Tm (e1 i) (subst-filler Ty e1 (A [ γ ]T) i)) (t [ γ ]t)) (t [ subst (λ z → Sub z Γ) e1 γ ]t)) (toPathP (sym (substComposite (Tm Δ) (subst-filler Ty (refl {x = Δ}) (A [ γ ]T)) (subst-[]T {A = A} {γ} {e = refl}) (t [ γ ]t)) ∙ cong (λ x → subst (Tm Δ) x (t [ γ ]t)) (TySet (A [ γ ]T) (A [ subst (λ z → Sub z Γ) (λ i → Δ) γ ]T) (subst-filler Ty (λ _ → Δ) (A [ γ ]T) ∙ subst-[]T {A = A} {γ}) (congS (A [_]T) (sym (transportRefl γ))) ) ∙ fromPathP (cong (t [_]t) (sym (transportRefl γ))))) e

{-
subst-Sub-[]t : ∀{Γ Δ}{A : Ty Γ}{t : Tm Γ A}{γ : Sub Δ Γ}{Δ'}{e : Δ ≡ Δ'} → PathP (λ i → Tm Δ' (subst-[]T {A = A} {γ} {e = e} i)) (transport (λ i → Tm (e i) (transp (λ j → Ty (e (i ∧ j))) (~ i) (A [ γ ]T))) (t [ γ ]t)) (t [ subst (λ z → Sub z Γ) e γ ]t)
subst-Sub-[]t {Γ} {Δ} {A} {t} {γ} {Δ'} {e} = {!!}
-}

{-
subst-lam-in : ∀{Γ}{A B : Ty Γ}{C : Ty (Γ ▹ A)}{t : Tm (Γ ▹ A) C}{e : A ≡ B} → lam (transport (λ i → Tm (Γ ▹ e i) C) t) ≡ ?
subst-lam-in = ?
-}

subst-lam-out : ∀{Γ}{A : Ty Γ}{B C : Ty (Γ ▹ A)}{t : Tm (Γ ▹ A) B}{e : B ≡ C} → subst (Tm Γ) (congS (Π A) e) (lam t) ≡ lam (subst (Tm (Γ ▹ A)) e t)
subst-lam-out {Γ} {A} {B} {C} {t} {e} = J (λ _ eq → subst (Tm Γ) (congS (Π A) eq) (lam t) ≡ lam (subst (Tm (Γ ▹ A)) eq t)) (transportRefl (lam t) ∙ congS lam (sym (transportRefl t))) e

subst-Ty-[]t : ∀{Γ Δ}{A : Ty Γ}{t : Tm Γ A}{γ : Sub Δ Γ}{B}{e : A ≡ B} → subst (λ z → Tm Δ (z [ γ ]T)) e (t [ γ ]t) ≡ subst (Tm Γ) e t [ γ ]t
subst-Ty-[]t {Γ} {Δ} {A} {t} {γ} {B} {e} = J (λ _ eq → subst (λ z → Tm Δ (z [ γ ]T)) eq (t [ γ ]t) ≡ subst (Tm Γ) eq t [ γ ]t) (transportRefl (t [ γ ]t) ∙ sym (congS (_[ γ ]t) (transportRefl t))) e

[∘]U : ∀{Γ Δ Θ}{Â : Tm Γ U}{γ : Sub Δ Γ}{δ : Sub Θ Δ} →  Â [ γ ∘ δ ]U ≡ Â [ γ ]U [ δ ]U
[∘]U {Γ} {Δ} {Θ} {Â} {γ} {δ} = sym (sym (fromPathP ([]U {γ = δ} {Â = Â [ γ ]U}))
                             ∙ cong (λ x → transport (λ i → Tm Θ (U[] {γ = δ} i)) (x [ δ ]t)) (sym (fromPathP ([]U {γ = γ} {Â = Â})))
                             ∙ cong (λ x → transport (λ i → Tm Θ (U[] {γ = δ} i)) x) (sym (subst-Ty-[]t {t = Â [ γ ]t} {e = U[] {γ = γ}}))
                             ∙ sym (substComposite (Tm Θ) (cong _[ δ ]T (U[] {γ = γ})) (U[] {γ = δ}) (Â [ γ ]t [ δ ]t))
                             ∙ cong (λ x → subst (Tm Θ) x (Â [ γ ]t [ δ ]t)) (TySet (U [ γ ]T [ δ ]T) U (cong _[ δ ]T (U[] {γ = γ}) ∙ U[] {γ = δ}) (sym ([∘]T {A = U} {γ = γ} {δ = δ}) ∙ U[] {γ = γ ∘ δ}))
                             ∙ substComposite (Tm Θ) (sym ([∘]T {A = U} {γ = γ} {δ = δ})) (U[] {γ = γ ∘ δ}) (Â [ γ ]t [ δ ]t)
                             ∙ cong (transport (λ i → Tm Θ (U[] {γ = γ ∘ δ} i))) (sym (fromPathP⁻ ([∘]t {γ = γ} {δ = δ} {a = Â})))
                             ∙ fromPathP ([]U {γ = γ ∘ δ} {Â = Â}))

[∘]Π : ∀ {Γ Δ Θ}{A : Ty Γ}{B : Ty (Γ ▹ A)}{t : Tm Γ (Π A B)}{γ : Sub Δ Γ}{δ : Sub Θ Δ} → PathP (λ i → Tm Θ (Π ([∘]T {A = A} {γ = γ} {δ = δ} i) (toPathP {A = λ i → Ty (Θ ▹ [∘]T {A = A} i)} {x = B [ (γ ∘ δ) ⁺ ]T} (subst-[]T {γ = (γ ∘ δ) ⁺} {e = congS (Θ ▹_) [∘]T} ∙ congS (B [_]T) (fromPathP (∘⁺ {Θ = Θ} {Γ = Γ} {A = A} {γ = γ} {δ = δ})) ∙ [∘]T {A = B} {γ = γ ⁺} {δ = δ ⁺}) i))) (t [ γ ∘ δ ]Π) (t [ γ ]Π [ δ ]Π)
[∘]Π {Γ} {Δ} {Θ} {A} {B} {t} {γ} {δ} = toPathP ( cong (transport (λ i → Tm Θ (Π ([∘]T {A = A} {γ = γ} {δ = δ} i) (toPathP {A = λ i → Ty (Θ ▹ [∘]T {A = A} i)} {x = B [ (γ ∘ δ) ⁺ ]T} (subst-[]T {A = B} {γ = (γ ∘ δ) ⁺} {e = congS (Θ ▹_) ([∘]T {A = A} {γ = γ} {δ = δ})} ∙ congS (B [_]T) (fromPathP (∘⁺ {A = A} {γ = γ} {δ = δ})) ∙ [∘]T {A = B} {γ = γ ⁺} {δ = δ ⁺}) i)))) (sym (fromPathP ([]Π {γ = γ ∘ δ} {t = t})))
                                               ∙ sym (substComposite (Tm Θ) (Π[] {A = A} {B = B} {γ = γ ∘ δ}) (cong₂ Π ([∘]T {A = A} {γ = γ} {δ = δ}) (toPathP {A = λ i → Ty (Θ ▹ [∘]T {A = A} i)} {x = B [ (γ ∘ δ) ⁺ ]T} (subst-[]T {A = B} {γ = (γ ∘ δ) ⁺} {e = congS (Θ ▹_) ([∘]T {A = A} {γ = γ} {δ = δ})} ∙ congS (B [_]T) (fromPathP (∘⁺ {A = A} {γ = γ} {δ = δ})) ∙ [∘]T {A = B} {γ = γ ⁺} {δ = δ ⁺}))) (t [ γ ∘ δ ]t))
                                               ∙ cong (λ x → subst (Tm Θ) x (t [ γ ∘ δ ]t)) (TySet (Π A B [ γ ∘ δ ]T) (Π (A [ γ ]T [ δ ]T) (B [ γ ⁺ ]T [ δ ⁺ ]T)) (Π[] {A = A} {B = B} {γ = γ ∘ δ} ∙ (cong₂ Π ([∘]T {A = A} {γ = γ} {δ = δ}) (toPathP {A = λ i → Ty (Θ ▹ [∘]T {A = A} i)} {x = B [ (γ ∘ δ) ⁺ ]T} (subst-[]T {A = B} {γ = (γ ∘ δ) ⁺} {e = congS (Θ ▹_) ([∘]T {A = A} {γ = γ} {δ = δ})} ∙ congS (B [_]T) (fromPathP (∘⁺ {A = A} {γ = γ} {δ = δ})) ∙ [∘]T {A = B} {γ = γ ⁺} {δ = δ ⁺})))) ([∘]T {A = Π A B} {γ = γ} {δ = δ} ∙ congS _[ δ ]T Π[] ∙ Π[]))
                                               ∙ substComposite (Tm Θ) ([∘]T {A = Π A B} {γ = γ} {δ = δ}) (congS _[ δ ]T Π[] ∙ Π[]) (t [ γ ∘ δ ]t)
                                               ∙ cong (subst (Tm Θ) (congS _[ δ ]T (Π[]) ∙ Π[])) (fromPathP ([∘]t {γ = γ} {a = t}))
                                               ∙ substComposite (Tm Θ) (congS _[ δ ]T Π[]) Π[] (t [ γ ]t [ δ ]t)
                                               ∙ congS (subst (Tm Θ) (Π[] {A = A [ γ ]T} {B = B [ γ ⁺ ]T} {γ = δ})) (subst-Ty-[]t {t = t [ γ ]t} {δ} {e = Π[] {A = A} {B = B} {γ = γ}})
                                               ∙ congS (λ x → transport (λ i → Tm Θ (Π[] {A = A [ γ ]T} {B = B [ γ ⁺ ]T} {γ = δ} i)) (x [ δ ]t)) (fromPathP ([]Π {γ = γ} {t = t}))
                                               ∙ fromPathP ([]Π {γ = δ} {t = t [ γ ]Π}))

---------------
-- isSet Con --
---------------
{-
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Unit renaming (Unit to ⊤)

infix 4 _≡ꟲᵒⁿ_

_≡ꟲᵒⁿ_ : Con → Con → Type
decode : {Γ Δ : Con} → Γ ≡ꟲᵒⁿ Δ → Γ ≡ Δ

◇ ≡ꟲᵒⁿ ◇ = ⊤
◇ ≡ꟲᵒⁿ _ ▹ _ = ⊥
_ ▹ _ ≡ꟲᵒⁿ ◇ = ⊥
Γ ▹ A ≡ꟲᵒⁿ Δ ▹ B = Σ (Γ ≡ꟲᵒⁿ Δ) λ e → PathP (λ i → Ty (decode {Γ} {Δ} e i)) A B

-- decode {Γ} {Δ} e = ?

decode {◇} {◇} _ = refl
decode {Γ ▹ A} {Δ ▹ B} (e , eT) = cong₂ _▹_ (decode {Γ} {Δ} e) eT

reflCode : {Γ : Con} → Γ ≡ꟲᵒⁿ Γ
decodeRefl : {Γ : Con} → decode (reflCode {Γ}) ≡ refl

reflCode {◇} = tt
reflCode {Γ ▹ A} = reflCode {Γ} , filler i1
  module reflCode-▹ where
  filler : (i : I) → PathP (λ j → Ty (decodeRefl {Γ} (~ i) j)) A A
  filler i = transport⁻-filler (λ i → PathP (λ j → Ty (decodeRefl {Γ} i j)) A A) refl i

decodeRefl {◇} i = refl
decodeRefl {Γ ▹ A} i = cong₂ _▹_ (decodeRefl {Γ} i) (reflCode-▹.filler Γ A (~ i))

encode : {Γ Δ : Con} → Γ ≡ Δ → Γ ≡ꟲᵒⁿ Δ
encode {Γ} {Δ} e = transport (λ i → Γ ≡ꟲᵒⁿ e i) (reflCode {Γ})

decodeEncode : {Γ Δ : Con} (e : Γ ≡ Δ) → decode {Γ} {Δ} (encode {Γ} {Δ} e) ≡ e
decodeEncode {Γ} {Δ} e =
  J (λ Δ e → decode {Γ} {Δ} (encode {Γ} {Δ} e) ≡ e)
    (cong (decode {Γ} {Γ}) (transportRefl _) ∙ decodeRefl {Γ})
    e

isProp≡ꟲᵒⁿ : (Γ Δ : Con) → isProp (Γ ≡ꟲᵒⁿ Δ)
isProp≡ꟲᵒⁿ ◇ ◇ = isPropUnit
isProp≡ꟲᵒⁿ (Γ ▹ A) (Δ ▹ B) =
  isPropΣ (isProp≡ꟲᵒⁿ Γ Δ) λ e → isOfHLevelPathP' 1 (TySet {Γ = Δ}) A B

ConSet : isSet Con
ConSet Γ Δ = isPropRetract (encode {Γ} {Δ}) (decode {Γ} {Δ}) (decodeEncode {Γ} {Δ}) (isProp≡ꟲᵒⁿ Γ Δ)
-}
-- Szumi's heterogeneous equality DSL
{-
_≡Ty[_]_ : ∀{Γ Δ} → Ty Γ → Γ ≡ Δ → Ty Δ → Type
A ≡Ty[ e ] B = PathP (λ i → Ty (e i)) A B
-}
