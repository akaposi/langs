
{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData renaming (znots to znotsFin; snotz to snotzFin)
open import Cubical.Data.FinData.Base
open import Cubical.Data.FinData.Order
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Sigma
import Cubical.Data.Sum as Sum
open Sum using (_⊎_; _⊎?_; inl; inr)
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function

module untyped-sk.pigeonhole where


private
  variable
    ℓ : Level
    m n : ℕ

any? : {P : Fin m → Type ℓ} → (∀ i → Dec (P i)) → Dec (Σ _ P)
any? {zero} {ℓ} {P} P? = no λ {()} 
any? {suc n} {ℓ} {P} P? with P? zero ⊎? any? (P? ∘ suc) 
... | yes (inl p) = yes (zero , p)
... | yes (inr (i , p)) = yes ((suc i) , p) 
... | no k = no λ where
  (zero , p) → k (inl p)
  (suc x , p) → k (inr (x , p))
  
punchOut : ∀ {m} {i j : Fin (suc m)} → (¬ i ≡ j) → Fin m
punchOut {m} {zero} {zero} i≢j = exfalso (i≢j refl)
punchOut {m} {zero} {suc j} x = j
punchOut {suc m} {suc i} {zero} x = zero
punchOut {suc m} {suc i} {suc j} i≢j = suc (punchOut (i≢j ∘  cong suc))

punchOut-injective : ∀ {m} {i j k : Fin (suc m)}
                     (i≢j : ¬ i ≡ j) (i≢k : ¬ i ≡ k) →
                     punchOut i≢j ≡ punchOut i≢k → j ≡ k

punchOut-injective {m} {zero} {zero} {_} 0≢0 _  _ = exfalso (0≢0 refl)
punchOut-injective {m} {zero} {suc j} {zero} _  0≢0 _ = exfalso (0≢0 refl)
punchOut-injective {m} {zero} {suc j} {suc k} _   _   pⱼ≡pₖ = cong suc pⱼ≡pₖ
punchOut-injective {suc m} {suc i} {zero} {zero} _ _ 0≡0 = refl
punchOut-injective {suc m} {suc i} {zero} {suc k} i≢j i≢k x = exfalso (znotsFin x)
punchOut-injective {suc m} {suc i} {suc j} {zero} i≢j i≢k x = exfalso (snotzFin x)
punchOut-injective {suc m} {suc i} {suc j} {suc k} i≢j i≢k pⱼ≡pₖ = cong suc (punchOut-injective (i≢j ∘ cong suc) (i≢k ∘ cong suc) (injSucFin pⱼ≡pₖ))

pigeonhole : ∀ {m n} → m <' n → (f : Fin n → Fin m) →
             Σ[ i ∈ Fin n ] Σ[ j ∈ Fin n ] (¬ i ≡ j) × (f i ≡ f j)
pigeonhole (s≤s z≤) f = exfalso (¬Fin0 (f zero))
pigeonhole (s≤s (s≤s m≤n)) f with any? (λ i → discreteFin (f zero) (f (suc i)))
... | yes  (j , p) = zero , suc j , (λ x → znotsFin x) , p
... | no ¬p with pigeonhole (s≤s m≤n) (λ j → punchOut (¬p  ∘ (j ,_ )) ) 
... | i , j , i≢j  , fᵢ≡fⱼ = suc i , (suc j , (i≢j ∘ injSucFin  , punchOut-injective (¬p  ∘  ((i ,_))) _ fᵢ≡fⱼ))
