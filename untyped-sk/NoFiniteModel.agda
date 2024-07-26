{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Vec
open import Cubical.Data.FinData hiding (znots)
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function

module untyped-sk.NoFiniteModel where

open import untyped-sk.Model
{-
data Fin : ℕ → Type where
  zero : ∀{n} → Fin (suc n)
  suc  : ∀{n} → Fin n → Fin (suc n)

iteFin : ∀{ℓ}(F : ℕ → Type ℓ) → (∀{n} → F (suc n)) → (∀{n} → F n → F (suc n)) → ∀{n} → Fin n → F n
iteFin F z s zero    = z
iteFin F z s (suc x) = s (iteFin F z s x)

recFin : ∀{ℓ}(F : ℕ → Type ℓ) → (∀{n} → F (suc n)) → (∀{n} → Fin n → F n → F (suc n)) → ∀{n} → Fin n → F n
recFin F z s zero    = z
recFin F z s (suc x) = s x (recFin F z s x)

predFin : ∀{n} → Fin n → Fin (suc n) → Fin n
predFin y x = recFin (λ n → {m : ℕ} → n ≡ 1 + m → Fin m → Fin m)
-- predFin y zero = y
  (λ _ y → y)
-- predFin y (suc n) = n
  (λ x' _ e _ → transport (cong (Fin ∘ predℕ) e) x')
  x refl y

zero≠suc : ∀{n}{x : Fin n} → zero ≡ suc x → ⊥
zero≠suc e = subst (iteFin (λ _ → Type) Unit (λ _ → ⊥)) e _

discreteFin : ∀{n} → Discrete (Fin n)
discreteFin zero zero    = yes refl
discreteFin zero (suc y) = no zero≠suc
discreteFin (suc x) zero = no λ e → zero≠suc (sym e)
discreteFin (suc x) (suc y) with discreteFin x y
... | yes e = yes (cong suc e)
... | no ¬e = no λ e → ¬e {!cong predFin e!}


isSetFin : ∀{n} → isSet (Fin n)
isSetFin = Discrete→isSet discreteFin


lookup : ∀{ℓ}{A : Set ℓ}{n : ℕ} → Vec A n → Fin n → A
lookup (i ∷ is) x with caseFin x
... | nothing = i
... | just x' = lookup is x'
-- lookup (x ∷ xs) zero    = x
-- lookup (x ∷ xs) (suc i) = lookup xs i
-}

caseFin' : ∀{n} → Fin n → Maybe (Σ ℕ λ m → (n ≡ 1 + m) × Fin m)
caseFin' zero    = nothing
caseFin' (suc x) = just (_ , refl , x)

caseFin : ∀{n} → Fin (suc n) → Maybe (Fin n)
caseFin x with caseFin' x
... | nothing = nothing
... | just (n , e , x') = just (transport (cong (Fin ∘ predℕ) (sym e)) x')

indVec : ∀{ℓ ℓ'}{A : Type ℓ'}(P : {n : ℕ} → Vec A n → Type ℓ) →
  P [] →
  ({n : ℕ}(a : A){as : Vec A n} → P as → P (a ∷ as)) →
  {n : ℕ}(as : Vec A n) → P as
indVec P n c []       = n
indVec P n c (a ∷ as) = c a (indVec P n c as)

indFin : ∀{ℓ}(P : {n : ℕ} → Fin n → Type ℓ) →
  (∀{n} → P (zero {n})) →
  (∀{n}{x : Fin n} → P x → P (suc x)) →
  ∀{n}(x : Fin n) → P x
indFin P z s zero = z
indFin P z s (suc x) = s (indFin P z s x)

subst-zero : {n m : ℕ}(e : suc n ≡ suc m) → subst Fin e zero ≡ zero
subst-zero {n} {m} e =
  subst Fin e zero
                                                    ≡⟨ cong (λ e → subst Fin e zero) (isSetℕ (suc n) (suc m) e (cong suc (cong predℕ e))) ⟩
  subst Fin (cong suc (cong predℕ e)) zero
                                                    ≡⟨ refl ⟩
  subst Fin (λ i → suc (predℕ (e i))) zero
                                                    ≡⟨ refl ⟩
  transport (λ i → Fin (suc (predℕ (e i)))) zero
                                                    ≡⟨ fromPathP (λ i → Fin.zero {predℕ (e i)}) ⟩
  zero
                                                    ∎

Fin1 : (x : Fin 1) → x ≡ zero
Fin1 x = 
  x
                         ≡⟨ sym (substRefl {B = Fin} x) ⟩
  subst Fin (λ _ → 1) x
                         ≡⟨ indFin
                              (λ {n} x → (e : n ≡ 1) → subst Fin e x ≡ zero)
                              subst-zero
                              {!!}
                              x refl ⟩
  zero
                         ∎

module _
  (m   : ℕ)
  (let n = suc (suc m))
  (_·'_ :  Fin n → Fin n → Fin n)
  (K' S' :  Fin n)
  (Kβ'  : {u f : Fin n} → (K' ·' u) ·' f ≡ u)
  (Sβ'  :  {f g u : Fin n} → ((S' ·' f) ·' g) ·' u ≡ (f ·' u) ·' (g ·' u))
  where

  M : Model
  M = record
    { Tm = Fin n ; TmSet = isSetFin ; _·_ = _·'_ ; K = K' ; S = S' ; Kβ = Kβ' ; Sβ = Sβ' }

  open Model M

  infixl 5 _·s_
  _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
  t ·s []       = t
  t ·s (u ∷ us) = t · u ·s us

  -- proj i x is the combinator version of λa₀...aᵢ.aₓ
  proj : ∀(i : ℕ) → Fin (suc i) → Tm
  proj zero    _ = I'                    -- λa₀.a₀
  proj (suc n) x with caseFin x
  ... | nothing = B · K · proj n zero
  ... | just x' = K · proj n x'

  postulate u : Tm

  projβ : (n : ℕ)(x : Fin (suc n))(us : Vec Tm (suc n)) → proj n x ·s us ≡ lookup x us
  -- projβ zero zero (u ∷ []) = Iβ
  projβ zero x us = indVec (λ {n} us → n ≡ 1 → (x : Fin n) → I' ·s us ≡ lookup x us)
    (λ e _ → exfalso (znots e))
    (λ u {us} _ e x' → indVec (λ {n} us → n ≡ 0 → ∀ x' → (I' ·' u) ·s us ≡ lookup x' (u ∷ us))
      (λ _ x' →
        (I' ·' u)
                                                         ≡⟨ Iβ ⟩
        u
                                                         ≡⟨ indFin
                                                              (λ {n} x' → (e : n ≡ 1) → u ≡ lookup (transport (λ i → Fin (e i)) x') (u ∷ []))
                                                              (λ e → cong (λ z → lookup z (u ∷ [])) (sym (subst-zero e)))
                                                              {!!}
                                                              x' refl ⟩
        lookup (transport (λ i → Fin one) x') (u ∷ [])
                                                         ≡⟨ cong (λ z → lookup z (u ∷ [])) (substRefl {B = Fin} x') ⟩
        lookup x' (u ∷ [])
                                                         ∎)
      (λ _ _ e → exfalso (znots (sym e)))
      us (cong predℕ e) x')
    us refl x
  projβ (suc n) = {!!}
  {-
  projβ (suc n) zero (u ∷ u' ∷ us) = (B · K · (proj n zero) · u · u' ·s us)
                                                ≡⟨ cong (λ x → (x · u') ·s us) Bβ ⟩ 
                                      (((K · (proj n zero · u)) · u') ·s us)
                                                ≡⟨ cong (_·s us) Kβ ⟩ 
                                      ((proj n zero · u) ·s us)
                                                ≡⟨ projβ n zero (u ∷ us) ⟩ 
                                      refl

  projβ (suc n) (suc x) (u ∷ u' ∷ us) =
     proj (suc n) (suc x) ·s (u ∷ u' ∷ us)
                                                            ≡⟨ cong (λ x → x · u' ·s us) Kβ ⟩
     proj n (transport (λ i → Fin (suc n)) x) · u' ·s us
                                                            ≡⟨ cong (λ z → proj n z · u' ·s us) (transportRefl x) ⟩
     proj n x · u' ·s us
                                                            ≡⟨ projβ n x (u' ∷ us) ⟩
     lookup (suc x) (u ∷ u' ∷ us)
                                          ∎-}

-- noFiniteModel : (M : Model {lzero})(n : ℕ) → Tm M ≡ Fin (2 + n) → ⊥
-- noFiniteModel = {!!}
