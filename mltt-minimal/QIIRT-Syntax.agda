{-# OPTIONS --cubical --no-postfix-projections --guardedness #-}

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
open import Cubical.Data.Sigma hiding (Sub)

open import mltt-minimal.Syntax
open import mltt-minimal.TakesYearsToLoadSubPi
open import mltt-minimal.TakesYearsToLoadLam
open import mltt-minimal.TakesYearsToLoadApp
open import mltt-minimal.DepModel

the : ∀{i}(A : Set i) → A → A
the _ x = x

private variable
  Γ Δ Θ : Con
  γ δ θ σ : Sub Δ Γ
  A B : Ty Γ
  a b Â t : Tm Γ A

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
ass∙ D {γ = γ} {δ} {θ} {γ∙ = γ∙} {δ∙} {θ∙} = implicitFunExt λ {Χ} → funExt λ ξ →
  let
    (θ∘ξ , ≡θ∘ξ) = θ∙ ξ
    (δ∘[θ∘ξ] , ≡δ∘[θ∘ξ]) = δ∙ θ∘ξ
    (γ∘[δ∘[θ∘ξ]] , ≡γ∘[δ∘[θ∘ξ]]) = γ∙ δ∘[θ∘ξ]
  in ΣPathP (refl , toPathP (SubSet (γ ∘ (δ ∘ θ) ∘ ξ) γ∘[δ∘[θ∘ξ]] (transport (λ i → ass {γ = γ} {δ = δ} {θ = θ} i ∘ ξ ≡ γ∘[δ∘[θ∘ξ]]) (ass ∙ congS (γ ∘ δ ∘_) ≡θ∘ξ ∙ ass ∙ congS (γ ∘_) ≡δ∘[θ∘ξ] ∙ ≡γ∘[δ∘[θ∘ξ]])) (ass ∙ congS (γ ∘_) (ass ∙ congS (δ ∘_) ≡θ∘ξ ∙ ≡δ∘[θ∘ξ]) ∙ ≡γ∘[δ∘[θ∘ξ]])))
id∙ D γ = γ , idl
idl∙ D {γ = γ} {γ∙ = γ∙} = implicitFunExt λ {Θ} → funExt λ δ →
  let
    (γ∘δ , ≡γ∘δ) = γ∙ δ
  in ΣPathP (refl , toPathP (SubSet (γ ∘ δ) γ∘δ (transport (λ i → idl {γ = γ} i ∘ δ ≡ γ∘δ) (ass ∙ congS (id ∘_) ≡γ∘δ ∙ idl)) ≡γ∘δ))
idr∙ D {γ = γ} {γ∙ = γ∙} = implicitFunExt λ {Θ} → funExt λ δ →
  let
    (γ∘δ , eγ∘δ) = γ∙ δ
  in ΣPathP (refl , toPathP (SubSet (γ ∘ δ) γ∘δ (transport (λ i → idr {γ = γ} i ∘ δ ≡ γ∘δ) (ass ∙ congS (γ ∘_) idl ∙ eγ∘δ)) eγ∘δ))
ε∙ D γ = ε , ◇η
◇η∙ D {σ = σ} {σ∙ = σ∙} = implicitFunExt λ {Θ} → funExt λ γ →
  let
    (σ∘γ , ≡σ∘γ) = σ∙ γ
  in ΣPathP (◇η , toPathP (SubSet (ε ∘ γ) ε (transport (λ i → ◇η i ∘ γ ≡ ◇η i) ≡σ∘γ) ◇η))
p∙ D γ = p ∘ γ , refl
⟨_⟩∙ D {Γ = Γ} {A} {t} {A∙ = A∙} tₛ {Δ} γ = let (t[γ]t* , e) = tₛ γ
                                            in subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) (snd (A∙ γ)) (γ ⁺) ∘ ⟨ t[γ]t* ⟩
                                             , ⟨⟩∘ {a = t} {γ = γ}
                                             ∙ congS (γ ⁺ ∘_) (congS ⟨_⟩ (fromPathP⁻ e)
                                             ∙ sym (subst-⟨⟩ {t = t[γ]t*} {e = sym (snd (A∙ γ))}))
                                             ∙ (subst-∘ₘ {γ = γ ⁺} {e = congS (Δ ▹_) (snd (A∙ γ))})
p∘⟨⟩∙ D {Γ} {A = A} {Δ} {a} {A∙ = A∙} {a∙} = implicitFunExt λ {Θ} → funExt λ γ →
  let
    (A[γ]T , eA) = A∙ γ
    (a[γ]t , ea) = a∙ γ
    pr = sym ass
       ∙ congS (_∘ ⟨ a[γ]t ⟩) (subst-∘ᵣ {Γ} {δ = γ ⁺} {e = congS (Θ ▹_) eA})
       ∙ congS (λ x → subst (λ z → Sub z Γ) (congS (Θ ▹_) eA) x ∘ ⟨ a[γ]t ⟩) p∘⁺
       ∙ congS (_∘ ⟨ a[γ]t ⟩) (sym (subst-∘ᵣ {γ = γ} {δ = p} {e = congS (Θ ▹_) eA}))
       ∙ congS (λ x → γ ∘ x ∘ ⟨ a[γ]t ⟩) (subst-p {e = eA})
       ∙ ass
       ∙ congS (γ ∘_) p∘⟨⟩
       ∙ idr
  in ΣPathP (pr , toPathP (SubSet (id ∘ γ) γ (transport (λ i → p∘⟨⟩ i ∘ γ ≡ pr i) (ass ∙ (λ i → p ∘ (⟨⟩∘ ∙ congS (γ ⁺ ∘_) (congS ⟨_⟩ (fromPathP⁻ ea) ∙ (sym (subst-⟨⟩ {A = A[γ]T} {t = a[γ]t} {e = sym eA}))) ∙ subst-∘ₘ {δ = ⟨ a[γ]t ⟩} {e = congS (Θ ▹_) eA}) i) ∙ refl)) idl))
_[_]T∙ D {Δ} {Γ} {A} {γ} A∙ γ∙ {Θ} δ = let (γ∘δ , e) = γ∙ δ in A [ γ∘δ ]T , sym ([∘]T {A = A} {γ = γ} {δ = δ}) ∙ congS (A [_]T) e
[∘]T∙ D {Δ} {Γ} {Θ} {A} {γ} {δ} {A∙ = A∙} {γ∙} {δ∙} = implicitFunExt λ {Ξ} → funExt λ θ →
  let
    (δ∘θ , ≡δ∘θ) = δ∙ θ
    (γ∘[δ∘θ] , ≡γ∘[δ∘θ]) = γ∙ δ∘θ
  in ΣPathP (congS (A [_]T) (sym ≡γ∘[δ∘θ]) ∙ [∘]T , toPathP {!!})
[id]T∙ D {Γ} {A} {A∙ = A∙} = {!!}
[p][⟨⟩]T∙ D {Γ} {A} {B} {b} {A∙ = A∙} {B∙} {b∙} = {!!}
U∙ D _ = U , U[]
U[]∙ D {Δ} {Γ} {γ} {γ∙ = γ∙} = {!!}
El∙ D {Γ = Γ} {Â} Âₛ {Δ} γ = let (Â[γ]t* , e) = Âₛ γ in El Â[γ]t* , El[] ∙ congS El (sym (fromPathP []U) ∙ fromPathP e)
Π∙ D {Γ = Γ} {A} {B} A∙ B∙ {Δ} γ = let (A[γ]T* , e1) = A∙ γ
                                       (B[γ⁺]T* , e2) = B∙ (subst (λ z → Sub (Δ ▹ z) (Γ ▹ A)) e1 (γ ⁺))
                                   in Π A[γ]T* B[γ⁺]T* , Π[] ∙ cong₂ Π e1 (toPathP (subst-[]T {A = B} {γ = γ ⁺} {e = congS (Δ ▹_) e1} ∙ e2))
_[_]t∙ D {A = A} {a = a} {γ = γ} {A∙ = A∙} a∙ γ∙ {Θ} δ =
  let
    (γ∘*δ , e3) = γ∙ δ
  in a [ γ∘*δ ]t , toPathP (substComposite (Tm Θ) (sym ([∘]T {A = A} {γ = γ})) (λ i → A [ e3 i ]T) (a [ γ ]t [ δ ]t) ∙ cong (transport (λ i → Tm Θ (A [ e3 i ]T))) (sym (fromPathP⁻ ([∘]t {a = a}))) ∙ fromPathP (cong (a [_]t) e3))
q∙ D {Γ = Γ} {A} {A∙ = A∙} {Δ} γ = subst (Tm Δ) (sym ([∘]T {A = A} {γ = p})) (q [ γ ]t) , toPathP (subst (λ x → subst (Tm Δ) x (q [ γ ]t) ≡ subst (Tm Δ) (λ i → [∘]T {A = A} {γ = p} {δ = γ} (~ i)) (q [ γ ]t)) (rUnit (sym ([∘]T {A = A} {γ = p} {δ = γ}))) refl)
q[⟨⟩]∙ D {Γ} {A} {a} {A∙ = A∙} {a∙} = {!!}
[∘]t∙ D {Δ} {Γ} {Θ} {A} {γ} {δ} {a} {A∙ = A∙} {γ∙} {δ∙} {a∙} = {!!}
[id]t∙ D {Γ} {A} {a} {A∙ = A∙} {a∙} = {!!}
_[_]U∙ D {Δ = Δ} {Γ} {Â} {γ} Â∙ γ∙ {Θ} δ =
  let (γ∘*δ , e) = γ∙ δ
  in Â [ γ∘*δ ]U , toPathP (fromPathP ([]U {γ = δ} {Â = Â [ γ ]U}) ∙ sym ([∘]U {Â = Â} {γ} {δ}) ∙ congS (Â [_]U) e)
[]U∙ D {Δ} {Γ} {γ} {Â} {γ∙ = γ∙} {Â∙} = {!!}
_⁺∙ D {γ = γ} γ∙ δ = γ ⁺ ∘ δ , refl
∘⁺∙ D {Δ} {Γ} {Θ} {γ} {δ} {A} {γ∙ = γ∙} {δ∙} {A∙} = {!!}
id⁺∙ D {Γ} {A} {A∙ = A∙} = {!!}
p∘⁺∙ D {Δ} {Γ} {γ} {A} {γ∙ = γ∙} {A∙} = {!!}
⟨⟩∘∙ D {Δ} {Γ} {A} {a} {γ} {A∙ = A∙} {a∙} {γ∙} = {!!}
p⁺∘⟨q⟩∙ D {Γ} {A} {A∙ = A∙} = {!!}
[p][⁺]T∙ D {Δ} {Γ} {A} {B} {γ} {A∙ = A∙} {B∙} {γ∙} = {!!}
[p⁺][⟨q⟩]T∙ D {Γ} {B} {A} {B∙ = B∙} {A∙} = {!!}
[⟨⟩][]T∙ D {Δ} {Γ} {B} {A} {a} {γ} {B∙ = B∙} {A∙} {a∙} {γ∙} = {!!}
El[]∙ D {Δ} {Γ} {Â} {γ} {Â∙ = Â∙} {γ∙} = {!!}
Π[]∙ D {Δ} {Γ} {A} {B} {γ} {A∙ = A∙} {B∙} {γ∙} = {!!}
q[⁺]∙ D {Δ} {Γ} {A} {γ} {A∙ = A∙} {γ∙} = {!!}
_[_]Π∙ D {Δ = Δ} {Γ} {A} {B} {γ} {Δ∙} {Γ∙} {A∙} {B∙} {f} f∙ γ∙ {Θ} δ = _[_]Π∙' {Δ} {Γ} {A} {B} {γ} {Δ∙} {Γ∙} {A∙} {B∙} {f} f∙ γ∙ {Θ} δ
[]Π∙ D {Γ} {Δ} {A} {B} {γ} {t} {A∙ = A∙} {B∙} {γ∙} {t∙} = {!!}
lam∙ D {Γ} {A} {B} {t} {Γ∙} {A∙} {B∙} t∙ {Δ} γ = lam∙' {Γ} {A} {B} {t} {Γ∙} {A∙} {B∙} t∙ {Δ} γ
app∙ D {Γ} {A} {B} {t} {a} {Γ∙} {A∙} {B∙} t∙ a∙ {Δ} γ = app∙' {Γ} {A} {B} {t} {a} {Γ∙} {A∙} {B∙} t∙ a∙ {Δ} γ
Πβ∙ D {Γ} {A} {B} {b} {a} {A∙ = A∙} {B∙} {b∙} {a∙} = {!!}
Πη∙ D {Γ} {A} {B} {t} {A∙ = A∙} {B∙} {t∙} = {!!}
lam[]∙ D {Δ} {Γ} {A} {B} {γ} {b} {A∙ = A∙} {B∙} {γ∙} {b∙} = {!!}
app[]∙ D {Δ} {Γ} {A} {B} {a} {γ} {t} {A∙ = A∙} {B∙} {a∙} {γ∙} {t∙} = {!!}
