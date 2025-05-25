{-# OPTIONS --cubical --no-postfix-projection #-}

module mltt-minimal.QIIRT-Syntax where

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import mltt-minimal.Syntax
open import mltt-minimal.DepModel

the : ∀{i}(A : Set i) → A → A
the _ x = x

infixl 8 _∘*_ _∘=_
infixl 9 _[_]T* _[_]t* _[_]T= _[_]t=
infixl 10 _⁺*

private variable
  Γ Δ Θ : Con
  γ δ θ σ : Sub Δ Γ
  A B : Ty Γ
  a b Â t : Tm Γ A

_[_]T* : Ty Γ → Sub Δ Γ → Ty Δ
_[_]T= : (A : Ty Γ)(γ : Sub Δ Γ) → A [ γ ]T ≡ A [ γ ]T*
_[_]t* : Tm Γ A → (γ : Sub Δ Γ) → Tm Δ (A [ γ ]T*)
_[_]t= : (a : Tm Γ A)(γ : Sub Δ Γ) → PathP (λ i → Tm Δ ((A [ γ ]T=) i)) (a [ γ ]t) (a [ γ ]t*)
_∘*_   : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
_∘=_   : (γ : Sub Δ Γ)(δ : Sub Θ Δ) → γ ∘ δ ≡ γ ∘* δ

_⁺*    : (γ : Sub Δ Γ) → Sub (Δ ▹ A [ γ ]T*) (Γ ▹ A)
_⁺* {Δ = Δ}{Γ = Γ}{A = A} γ = subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) (A [ γ ]T=) (γ ⁺)

-- _[_]T* _[_]T= _[_]t* _[_]t= _∘*_ _∘=_ defined at the same time in D
D : DepModel {ℓ-zero} {ℓ-zero} {ℓ-zero} {ℓ-zero}
Con∙ D _ = ⊤
Sub∙ D {Δ} {Γ} _ _ γ = ∀ {Θ} → (δ : Sub Θ Δ) → Σ (Sub Θ Γ) (λ θ → γ ∘ δ ≡ θ)
Ty∙ D {Γ} _ A = ∀ {Δ} → (γ : Sub Δ Γ) → Σ (Ty Δ) (λ A[γ]T* → A [ γ ]T ≡ A[γ]T*)
Tm∙ D {Γ} {A} _ s t = ∀ {Δ} → (γ : Sub Δ Γ) → Σ (Tm Δ (fst (s γ))) (λ a[γ]t* → PathP (λ i → Tm Δ (snd (s γ) i)) (t [ γ ]t) a[γ]t*)
_▹∙_ D _ _ = tt
◇∙ D = tt
SubSet∙ D = isSetImplicitΠ λ Θ → isSetΠ λ δ → isContr→isOfHLevel 2 (isContrSingl (_ ∘ δ))
TySet∙ D = isSetImplicitΠ λ Δ → isSetΠ λ γ → isContr→isOfHLevel 2 (isContrSingl (_ [ γ ]T))
TmSet∙ D {A∙ = A∙} = isSetImplicitΠ λ Δ → isSetΠ λ γ → isContr→isOfHLevel 2 (isContrSinglP (λ i → Tm Δ (snd (A∙ γ) i)) (_ [ γ ]t))
_∘∙_ D {γ = γ} {δ} γ∘* δ∘* {Ξ} θ = let (δ∘*θ    , δ∘*θ≡   ) = δ∘* θ
                                       (γ∘*δ∘*θ , γ∘*δ∘*θ≡) = γ∘* δ∘*θ
                                   in γ∘*δ∘*θ , ass ∙ congS (γ ∘_) δ∘*θ≡ ∙ γ∘*δ∘*θ≡
ass∙ D = {!!}
id∙ D γ = γ , idl
idl∙ D = {!!}
idr∙ D = {!!}
ε∙ D γ = ε , ◇η
◇η∙ D = {!!}
p∙ D γ = p ∘ γ , refl
_⁺∙ D {γ = γ} γ∙ δ = γ ⁺ ∘ δ , refl
⟨_⟩∙ D {Γ = Γ} {A} {t} {A∙ = A∙} tₛ {Δ} γ = let (t[γ]t* , e) = tₛ γ
                                            in subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) (snd (A∙ γ)) (γ ⁺) ∘ ⟨ t[γ]t* ⟩
                                             , ⟨⟩∘ {a = t} {γ = γ}
                                             ∙ congS (γ ⁺ ∘_) (congS ⟨_⟩ (fromPathP⁻ e)
                                             ∙ sym (subst-⟨⟩ {t = t[γ]t*} {e = sym (snd (A∙ γ))}))
                                             ∙ (subst-∘ₘ {γ = γ ⁺} {e = congS (Δ ▹_) (snd (A∙ γ))})
∘⁺∙ D = {!!}
id⁺∙ D = {!!}
p∘⁺∙ D = {!!}
p∘⟨⟩∙ D = {!!}
_[_]T∙ D {Δ} {Γ} {A} {γ} A∙ γ∙ {Θ} δ = let (γ∘δ , e) = γ∙ δ in A [ γ∘δ ]T , sym [∘]T ∙ congS (A [_]T) e
[∘]T∙ D = {!!}
[id]T∙ D = {!!}
[p][⟨⟩]T∙ D = {!!}
[p][⁺]T∙ D = {!!}
U∙ D _ = U , U[]
U[]∙ D = {!!}
El∙ D {Γ = Γ} {Â} Âₛ {Δ} γ = let (Â[γ]t* , e) = Âₛ γ in El Â[γ]t* , El[] ∙ cong El (sym (fromPathP []U) ∙ fromPathP e)
Π∙ D {Γ = Γ} {A} {B} A∙ B∙ {Δ} γ = let (A[γ]T* , e1) = A∙ γ
                                       (B[γ⁺]T* , e2) = B∙ (subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺))
                                   in Π A[γ]T* B[γ⁺]T* , Π[] ∙ cong₂ Π e1 (toPathP (subst-[]T {A = B} {γ = γ ⁺} {e = congS (Δ ▹_) e1} ∙ e2))
Π[]∙ D = {!!}
_[_]t∙ D {A = A} {a = a} {γ = γ} {A∙ = A∙} a∙ γ∙ {Θ} δ =
  let
    (A[γ]T* , e1) = A∙ γ
    (a[γ]t* , e2) = a∙ γ
    (γ∘*δ , e3) = γ∙ δ
  in a [ γ∘*δ ]t , toPathP (substComposite (Tm Θ) (sym ([∘]T {A = A} {γ = γ})) (λ i → A [ e3 i ]T) (a [ γ ]t [ δ ]t) ∙ cong (transport (λ i → Tm Θ (A [ e3 i ]T))) (sym (fromPathP⁻ ([∘]t {a = a}))) ∙ fromPathP (cong (a [_]t) e3))
q∙ D {Γ = Γ} {A} {A∙ = A∙} {Δ} γ = subst (Tm Δ) (sym ([∘]T {A = A} {γ = p})) (q [ γ ]t) , toPathP (subst (λ x → subst (Tm Δ) x (q [ γ ]t) ≡ subst (Tm Δ) (λ i → [∘]T {A = A} {γ = p} {δ = γ} (~ i)) (q [ γ ]t)) (rUnit (sym ([∘]T {A = A} {γ = p} {δ = γ}))) refl)
q[⟨⟩]∙ D = {!!}
q[⁺]∙ D = {!!}
[∘]t∙ D = {!!}
[id]t∙ D = {!!}
_[_]U∙ D {Δ = Δ} {Γ} {Â} {γ} Â∙ γ∙ {Θ} δ =
  let (γ∘*δ , e) = γ∙ δ
  in Â [ γ∘*δ ]U , toPathP (fromPathP ([]U {γ = δ} {Â = Â [ γ ]U}) ∙ sym ([∘]U {Â = Â} {γ} {δ}) ∙ cong (Â [_]U) e)
[]U∙ D = {!!}
_[_]Π∙ D {Δ = Δ} {Γ} {A} {B} {γ} {A∙ = A∙} {B∙} {f} f∙ γ∙ {Θ} δ =
  let (γ∘*δ , e1) = γ∙ δ
      (f[γ∘*δ] , e2) = f∙ γ∘*δ
  in {!!} -- f [ γ ]Π [ δ ]t = f [ γ ∘ δ ]Π
[]Π∙ D = {!!}
lam∙ D {Γ} {A} {B} {t} {A∙ = A∙} {B∙} t∙ {Δ} γ =
  let
    (A[γ]T , e1) = A∙ γ
    (B[γ⁺]T , e2) = B∙ (subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺))
    (t[γ⁺]t , e3) = t∙ (subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺))
  in lam t[γ⁺]t , toPathP {!!}
app∙ D = {!!}
Πβ∙ D = {!!}
Πη∙ D = {!!}
lam[]∙ D = {!!}
app[]∙ D = {!!}
⟨⟩∘∙ D = {!!}
p⁺∘⟨q⟩∙ D = {!!}
[p⁺][⟨q⟩]T∙ D = {!!}
[⟨⟩][]T∙ D = {!!}
El[]∙ D = {!!}

module D = DepModel D

A [ γ ]T* = {!!}
{-
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
-}

A [ γ ]T= = {!!}

_∘*_ γ δ = {!!}

_∘=_ {Δ} {Γ} {Θ} γ δ = {!!}

a [ γ ]t* = {!!}

a [ γ ]t= = {!!}
