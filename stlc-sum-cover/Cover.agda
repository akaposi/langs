{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive 
open import Cubical.Foundations.Prelude hiding (_,_; Sub) -- hiding doesnt work?
open import Cubical.Relation.Binary.Base 
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary 
open import Cubical.Data.Sigma hiding (_,_; Sub)
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Nat
module stlc-sum-cover.Cover where
open import stlc-sum-cover.Syntax as S
open import stlc-sum-cover.Weakening as W
open import stlc-sum-cover.NormalForm as N

data Cov (P : S.Con → Type) (Γ : S.Con) : Type where
  return : P Γ → Cov P Γ
  abort  : N.Ne Γ S.⊥ₗ → Cov P Γ
  case   : ∀ {A B} → N.Ne Γ (A S.+ B) 
         → Cov P (Γ S.▸ A) 
         → Cov P (Γ S.▸ B) 
         → Cov P Γ

fmapCov : ∀ {P Q : S.Con → Type} {Γ} → (∀ {Δ} → P Δ → Q Δ) → Cov P Γ → Cov Q Γ
fmapCov f (return x) = return (f x)
fmapCov f (abort x) = abort x
fmapCov f (case ne c1 c2) = case ne (fmapCov f c1) (fmapCov f c2)

-- wk - Cov
mapCov : ∀ {P Q : S.Con → Type} {Γ}
       → (∀ {Δ} → W.Wk Δ Γ → P Δ → Q Δ)
       → Cov P Γ → Cov Q Γ
mapCov f (return x) = return (f W.id' x)
mapCov f (abort x) = abort x
mapCov f (case ne c1 c2) = case ne (mapCov (λ w p → f ((W.id' ∘p) ∘' w) p) c1) (mapCov (λ w p → f ((W.id' ∘p) ∘' w) p) c2) 

joinCov : ∀ {P : S.Con → Type} {Γ} → Cov (Cov P) Γ → Cov P Γ
joinCov (return c) = c
joinCov (abort x) = abort x
joinCov (case ne c1 c2) = case ne (joinCov c1) (joinCov c2)

-- Weakening for the Cover Monad
wkCov : ∀ {P : S.Con → Type} {Δ Γ} 
      → (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
      → Cov P Γ → W.Wk Δ Γ → Cov P Δ
wkCov wkP (return x) ρ = return (wkP x ρ)
wkCov wkP (abort x) ρ = abort (x N.[ ρ ]ᴺᵉ)
wkCov wkP (case ne c1 c2) ρ = case (ne N.[ ρ ]ᴺᵉ) (wkCov wkP c1 (ρ W.↑')) (wkCov wkP c2 (ρ W.↑'))

runTm : ∀ {Γ Aˢ} → Cov (λ Δ → S.Tm Δ Aˢ) Γ → S.Tm Γ Aˢ
runTm (return t) = t
runTm (abort ne) = S.exfalsoₗ (N.Ne-emb ne)
runTm (case ne c1 c2) = S.caseₗ (N.Ne-emb ne) (runTm c1) (runTm c2)

wk-p-eq : ∀ {Γ A} → W.Wk-emb (W.id' W.∘p) ≡ S.p {Γ = Γ} {A = A}
wk-p-eq = cong (_∘ p)  Wk-emb-id  ∙  S.idl p

lam-exfalso : ∀ {Γ A B} (t : S.Tm Γ S.⊥ₗ) 
            → S.lam (S.exfalsoₗ {A = B} (t S.[ W.Wk-emb (W.id' W.∘p) ])) ≡ S.exfalsoₗ {A = A S.⇒ B} t
lam-exfalso {Γ} {A} {B} t = 
    (λ i → S.lam (S.exfalsoₗ {A = B} (t S.[ wk-p-eq {Γ} {A} i ])))
  ∙ (λ i → S.lam (sym (S.π-⇒0 {A = A} {B = B} (t S.[ S.p ]) S.q) i))
  ∙ (λ i → S.lam (S.app (sym (S.exfalsoₗ-[] {A = A S.⇒ B} t S.p) i) S.q))
  ∙ S.⇒-η (S.exfalsoₗ {A = A S.⇒ B} t)

runNf : ∀ {Γ Aˢ} → Cov (λ Δ → N.Nf Δ Aˢ) Γ → N.Nf Γ Aˢ
runNf (return nf) = nf
runNf {Aˢ = S.⊥ₗ} (abort ne) = N.exfalsoNe ne
runNf {Aˢ = A S.⇒ B} (abort ne) = N.lam (runNf (abort (ne N.[ W.id' W.∘p ]ᴺᵉ)))
runNf {Aˢ = A S.+ B} (abort ne) = N.exfalsoNe ne
runNf (case ne c1 c2) = N.caseNe ne (runNf c1) (runNf c2)

embCov : ∀ {Γ Aˢ} → Cov (λ Δ → N.Nf Δ Aˢ) Γ → S.Tm Γ Aˢ
embCov (return nf) = N.Nf-emb nf
embCov (abort ne) = S.exfalsoₗ (N.Ne-emb ne)
embCov (case ne c1 c2) = S.caseₗ (N.Ne-emb ne) (embCov c1) (embCov c2)

emb-runNf : ∀ {Γ Aˢ} (c : Cov (λ Δ → N.Nf Δ Aˢ) Γ) → N.Nf-emb (runNf c) ≡ embCov c
emb-runNf (return nf) = refl
emb-runNf {Aˢ = S.⊥ₗ} (abort ne) = refl
emb-runNf {Aˢ = A S.⇒ B} (abort ne) = 
    cong S.lam (emb-runNf {Aˢ = B} (abort (ne N.[ W.id' W.∘p ]ᴺᵉ)))
  ∙ cong S.lam (cong S.exfalsoₗ (N.Ne-emb-[] ne (W.id' W.∘p)))
  ∙ lam-exfalso (N.Ne-emb ne)
emb-runNf {Aˢ = A S.+ B} (abort ne) = refl
emb-runNf (case ne c1 c2) = λ i → S.caseₗ (N.Ne-emb ne) (emb-runNf c1 i) (emb-runNf c2 i)

collapseNf : ∀ {Γ Aˢ Bˢ} → Cov (λ Δ → N.Nf Δ Bˢ) (Γ S.▸ Aˢ) → N.Nf Γ (Aˢ S.⇒ Bˢ)
collapseNf c = N.lam (runNf c)

emb-collapseNf : ∀ {Γ Aˢ Bˢ} (c : Cov (λ Δ → N.Nf Δ Bˢ) (Γ S.▸ Aˢ))
               → N.Nf-emb (collapseNf c) ≡ S.lam (embCov c)
emb-collapseNf c = cong S.lam (emb-runNf c)

collapseNf-runNf : ∀ {Γ Aˢ Bˢ} (c : Cov (λ Δ → N.Nf Δ Bˢ) (Γ S.▸ Aˢ)) → collapseNf c ≡ N.lam (runNf c)
collapseNf-runNf c = refl

wk-comm : ∀ {X Y A} (ρ : W.Wk Y X) → ρ W.∘' (W.id' W.∘p) ≡ (W.id' W.∘p) W.∘' ( W._↑' {A = A} ρ)
wk-comm ρ =( λ i → (idr' ρ i ∘p)) ∙ ( λ i → (idl' ρ (~ i) ∘p)) 

runNf-[]-abort : ∀ {X Y Aˢ} (ne : N.Ne X S.⊥ₗ) (ρ : W.Wk Y X) 
               → runNf {Aˢ = Aˢ} (abort (ne N.[ ρ ]ᴺᵉ)) ≡ runNf {Aˢ = Aˢ} (abort ne) N.[ ρ ]ᴺᶠ
runNf-[]-abort {Aˢ = S.⊥ₗ} ne ρ = refl
runNf-[]-abort {Aˢ = A S.⇒ B} ne ρ = cong N.lam (
    (λ i → runNf {Aˢ = B} (abort (sym (N.[]ᴺᵉ-∘ ne ρ (W.id' W.∘p)) i)))
  ∙ (λ i → runNf {Aˢ = B} (abort (ne N.[ wk-comm ρ i ]ᴺᵉ)))
  ∙ (λ i → runNf {Aˢ = B} (abort (N.[]ᴺᵉ-∘ ne (W.id' W.∘p) (ρ W.↑') i)))
  ∙ runNf-[]-abort {Aˢ = B} (ne N.[ W.id' W.∘p ]ᴺᵉ) (ρ W.↑')
  )
runNf-[]-abort {Aˢ = A S.+ B} ne ρ = refl

runNf-[] : ∀ {X Y Aˢ} (c : Cov (λ Δ → N.Nf Δ Aˢ) X) (ρ : W.Wk Y X)
         → runNf (wkCov (λ nf w → nf N.[ w ]ᴺᶠ) c ρ) ≡ runNf c N.[ ρ ]ᴺᶠ
runNf-[] (return nf) ρ = refl
runNf-[] {Aˢ = S.⊥ₗ} (abort ne) ρ = refl
runNf-[] {Aˢ = A S.⇒ B} (abort ne) ρ = runNf-[]-abort ne ρ
runNf-[] {Aˢ = A S.+ B} (abort ne) ρ = refl
runNf-[] (case ne c1 c2) ρ = λ i → N.caseNe (ne N.[ ρ ]ᴺᵉ) (runNf-[] c1 (ρ W.↑') i) (runNf-[] c2 (ρ W.↑') i)

collapseNf-[] : ∀ {X Y Aˢ Bˢ} (c : Cov (λ Δ → N.Nf Δ Bˢ) (X S.▸ Aˢ)) (ρ : W.Wk Y X)
              → collapseNf (wkCov (λ nf w → nf N.[ w ]ᴺᶠ) c (ρ W.↑')) ≡ collapseNf c N.[ ρ ]ᴺᶠ
collapseNf-[] c ρ = cong N.lam (runNf-[] c (ρ W.↑'))

embCov-[] : ∀ {X Y Aˢ} (c : Cov (λ Δ → N.Nf Δ Aˢ) X) (ρ : W.Wk Y X)
          → embCov (wkCov (λ nf w → nf N.[ w ]ᴺᶠ) c ρ) ≡ embCov c S.[ W.Wk-emb ρ ]
embCov-[] (return nf) ρ = N.Nf-emb-[] nf ρ
embCov-[] (abort ne) ρ = (λ i → S.exfalsoₗ (N.Ne-emb-[] ne ρ i)) ∙ sym (S.exfalsoₗ-[] (N.Ne-emb ne) (W.Wk-emb ρ))
embCov-[] (case ne c1 c2) ρ = (λ i → S.caseₗ (N.Ne-emb-[] ne ρ i) (embCov-[] c1 (ρ W.↑') i) (embCov-[] c2 (ρ W.↑') i)) ∙ sym (S.caseₗ-[] (N.Ne-emb ne) (embCov c1) (embCov c2) (W.Wk-emb ρ))

open import Cubical.Data.Empty renaming (rec to exfalso)

private
  wkP⊥ : ∀ {X Y} → ⊥ → W.Wk Y X → ⊥
  wkP⊥ v _ = exfalso v

wkCov⊥-∘ : ∀ {X Y Z} (c : Cov (λ _ → ⊥) X) (x : W.Wk Y X) (y : W.Wk Z Y)
          → wkCov wkP⊥ c (x W.∘' y) ≡ wkCov wkP⊥ (wkCov wkP⊥ c x) y
wkCov⊥-∘ (return v) x y = exfalso v
wkCov⊥-∘ (abort ne) x y = λ i → abort (N.[]ᴺᵉ-∘ ne x y i)
wkCov⊥-∘ (case ne c1 c2) x y = λ i → case (N.[]ᴺᵉ-∘ ne x y i) (wkCov⊥-∘ c1 (x W.↑') (y W.↑') i) (wkCov⊥-∘ c2 (x W.↑') (y W.↑') i)

wkCov⊥-id : ∀ {X} (c : Cov (λ _ → ⊥) X) → wkCov wkP⊥ c W.id' ≡ c
wkCov⊥-id (return v) = exfalso v
wkCov⊥-id (abort ne) = λ i → abort (N.[]ᴺᵉ-id ne i)
wkCov⊥-id (case ne c1 c2) = λ i → case (N.[]ᴺᵉ-id ne i) (wkCov⊥-id c1 i) (wkCov⊥-id c2 i)

runTm-fmap⊥-wkCov : ∀ {X Y Aˢ} (c : Cov (λ _ → ⊥) X) (x : W.Wk Y X)
                   → runTm {Aˢ = Aˢ} (fmapCov (λ v → exfalso v) (wkCov wkP⊥ c x)) ≡ runTm (fmapCov (λ v → exfalso v) c) S.[ W.Wk-emb x ]
runTm-fmap⊥-wkCov (return v) x = exfalso v
runTm-fmap⊥-wkCov (abort ne) x = (λ i → S.exfalsoₗ (N.Ne-emb-[] ne x i)) ∙ sym (S.exfalsoₗ-[] (N.Ne-emb ne) (W.Wk-emb x))
runTm-fmap⊥-wkCov (case ne c1 c2) x = (λ i → S.caseₗ (N.Ne-emb-[] ne x i) (runTm-fmap⊥-wkCov c1 (x W.↑') i) (runTm-fmap⊥-wkCov c2 (x W.↑') i)) ∙ sym (S.caseₗ-[] (N.Ne-emb ne) (runTm (fmapCov (λ v → exfalso v) c1)) (runTm (fmapCov (λ v → exfalso v) c2)) (W.Wk-emb x))

fmap⊥-wkCov : ∀ {X Y Aˢ} (c : Cov (λ _ → ⊥) X) (x : W.Wk Y X)
             → fmapCov {Q = λ Δ → N.Nf Δ Aˢ} (λ v → exfalso v) (wkCov wkP⊥ c x) ≡ wkCov (λ nf w → nf N.[ w ]ᴺᶠ) (fmapCov (λ v → exfalso v) c) x
fmap⊥-wkCov (return v) x = exfalso v
fmap⊥-wkCov (abort ne) x = refl
fmap⊥-wkCov (case ne c1 c2) x = λ i → case (ne N.[ x ]ᴺᵉ) (fmap⊥-wkCov c1 (x W.↑') i) (fmap⊥-wkCov c2 (x W.↑') i)

embCov-runTm-fmap⊥ : ∀ {X Aˢ} (c : Cov (λ _ → ⊥) X)
                    → embCov {Aˢ = Aˢ} (fmapCov (λ v → exfalso v) c) ≡ runTm (fmapCov (λ v → exfalso v) c)
embCov-runTm-fmap⊥ (return v) = exfalso v
embCov-runTm-fmap⊥ (abort ne) = refl
embCov-runTm-fmap⊥ (case ne c1 c2) = λ i → S.caseₗ (N.Ne-emb ne) (embCov-runTm-fmap⊥ c1 i) (embCov-runTm-fmap⊥ c2 i)

joinCov-wkCov⊥ : ∀ {X Y} (c : Cov (Cov (λ _ → ⊥)) X) (x : W.Wk Y X)
               → joinCov (wkCov (λ c' w → wkCov wkP⊥ c' w) c x) ≡ wkCov wkP⊥ (joinCov c) x
joinCov-wkCov⊥ (return c') x = refl
joinCov-wkCov⊥ (abort ne) x = refl
joinCov-wkCov⊥ (case ne c1 c2) x = λ i → case (ne N.[ x ]ᴺᵉ) (joinCov-wkCov⊥ c1 (x W.↑') i) (joinCov-wkCov⊥ c2 (x W.↑') i)

-- runTm ∘ fmapCov (runTm ∘ fmapCov exfalso) ≡ runTm ∘ fmapCov exfalso ∘ joinCov 
runTm-fmap-joinCov⊥ : ∀ {X Aˢ} (c : Cov (Cov (λ _ → ⊥)) X)
                     → runTm {Aˢ = Aˢ} (fmapCov (λ v → exfalso v) (joinCov c)) ≡ runTm (fmapCov (λ a → runTm (fmapCov (λ v → exfalso v) a)) c)
runTm-fmap-joinCov⊥ (return c') = refl
runTm-fmap-joinCov⊥ (abort ne) = refl
runTm-fmap-joinCov⊥ (case ne c1 c2) = λ i → S.caseₗ (N.Ne-emb ne) (runTm-fmap-joinCov⊥ c1 i) (runTm-fmap-joinCov⊥ c2 i)


wkCov-∘ : ∀ {P : S.Con → Type} {X Y Z}
         (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
         (wkP-∘ : ∀ {X Y Z} (p : P X) (x : W.Wk Y X) (y : W.Wk Z Y) → wkP p (x W.∘' y) ≡ wkP (wkP p x) y)
         (c : Cov P X) (x : W.Wk Y X) (y : W.Wk Z Y)
       → wkCov wkP c (x W.∘' y) ≡ wkCov wkP (wkCov wkP c x) y
wkCov-∘ wkP wkP-∘ (return x₁) x y = cong return (wkP-∘ x₁ x y)
wkCov-∘ wkP wkP-∘ (abort ne) x y = λ i → abort (N.[]ᴺᵉ-∘ ne x y i)
wkCov-∘ wkP wkP-∘ (case ne c1 c2) x y = λ i → case (N.[]ᴺᵉ-∘ ne x y i) (wkCov-∘ wkP wkP-∘ c1 (x W.↑') (y W.↑') i) (wkCov-∘ wkP wkP-∘ c2 (x W.↑') (y W.↑') i)

wkCov-id : ∀ {P : S.Con → Type} {X}
          (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
          (wkP-id : ∀ {X} (p : P X) → wkP p W.id' ≡ p)
          (c : Cov P X)
        → wkCov wkP c W.id' ≡ c
wkCov-id wkP wkP-id (return x) = cong return (wkP-id x)
wkCov-id wkP wkP-id (abort ne) = λ i → abort (N.[]ᴺᵉ-id ne i)
wkCov-id wkP wkP-id (case ne c1 c2) = λ i → case (N.[]ᴺᵉ-id ne i) (wkCov-id wkP wkP-id c1 i) (wkCov-id wkP wkP-id c2 i)

joinCov-wkCov : ∀ {P : S.Con → Type} {X Y}
              (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
              (c : Cov (Cov P) X) (x : W.Wk Y X)
            → joinCov (wkCov (λ c' w → wkCov wkP c' w) c x) ≡ wkCov wkP (joinCov c) x
joinCov-wkCov wkP (return c') x = refl
joinCov-wkCov wkP (abort ne) x = refl
joinCov-wkCov wkP (case ne c1 c2) x = λ i → case (ne N.[ x ]ᴺᵉ) (joinCov-wkCov wkP c1 (x W.↑') i) (joinCov-wkCov wkP c2 (x W.↑') i)

runTm-fmapCov-joinCov : ∀ {P : S.Con → Type} {X Aˢ}
                       (f : ∀ {Δ} → P Δ → S.Tm Δ Aˢ)
                       (c : Cov (Cov P) X)
                     → runTm (fmapCov f (joinCov c)) ≡ runTm (fmapCov (λ c' → runTm (fmapCov f c')) c)
runTm-fmapCov-joinCov f (return c') = refl
runTm-fmapCov-joinCov f (abort ne) = refl
runTm-fmapCov-joinCov f (case ne c1 c2) = λ i → S.caseₗ (N.Ne-emb ne) (runTm-fmapCov-joinCov f c1 i) (runTm-fmapCov-joinCov f c2 i)

runTm-fmapCov-wkCov : ∀ {P : S.Con → Type} {X Y Aˢ}
                     (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
                     (f : ∀ {Δ} → P Δ → S.Tm Δ Aˢ)
                     (f-nat : ∀ {X Y} (p : P X) (w : W.Wk Y X) → f (wkP p w) ≡ f p S.[ W.Wk-emb w ])
                     (c : Cov P X) (x : W.Wk Y X)
                   → runTm (fmapCov f (wkCov wkP c x)) ≡ runTm (fmapCov f c) S.[ W.Wk-emb x ]
runTm-fmapCov-wkCov wkP f f-nat (return x₁) x = f-nat x₁ x
runTm-fmapCov-wkCov wkP f f-nat (abort ne) x = (λ i → S.exfalsoₗ (N.Ne-emb-[] ne x i)) ∙ sym (S.exfalsoₗ-[] (N.Ne-emb ne) (W.Wk-emb x))
runTm-fmapCov-wkCov wkP f f-nat (case ne c1 c2) x = (λ i → S.caseₗ (N.Ne-emb-[] ne x i) (runTm-fmapCov-wkCov wkP f f-nat c1 (x W.↑') i) (runTm-fmapCov-wkCov wkP f f-nat c2 (x W.↑') i)) ∙ sym (S.caseₗ-[] (N.Ne-emb ne) (runTm (fmapCov f c1)) (runTm (fmapCov f c2)) (W.Wk-emb x))

fmapCov-wkCov : ∀ {P Q : S.Con → Type} {X Y}
              (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
              (wkQ : ∀ {X Y} → Q X → W.Wk Y X → Q Y)
              (f : ∀ {Δ} → P Δ → Q Δ)
              (f-nat : ∀ {X Y} (p : P X) (w : W.Wk Y X) → f (wkP p w) ≡ wkQ (f p) w)
              (c : Cov P X) (x : W.Wk Y X)
            → fmapCov f (wkCov wkP c x) ≡ wkCov wkQ (fmapCov f c) x
fmapCov-wkCov wkP wkQ f f-nat (return x₁) x = cong return (f-nat x₁ x)
fmapCov-wkCov wkP wkQ f f-nat (abort ne) x = refl
fmapCov-wkCov wkP wkQ f f-nat (case ne c1 c2) x = λ i → case (ne N.[ x ]ᴺᵉ) (fmapCov-wkCov wkP wkQ f f-nat c1 (x W.↑') i) (fmapCov-wkCov wkP wkQ f f-nat c2 (x W.↑') i)

embCov-joinCov : ∀ {X Aˢ} (c : Cov (Cov (λ Δ → N.Nf Δ Aˢ)) X)
               → embCov (joinCov c) ≡ runTm (fmapCov embCov c)
embCov-joinCov (return c') = refl
embCov-joinCov (abort ne) = refl
embCov-joinCov (case ne c1 c2) = λ i → S.caseₗ (N.Ne-emb ne) (embCov-joinCov c1 i) (embCov-joinCov c2 i)

-- joinCov-fmapCov interaction: joinCov ∘ fmapCov (fmapCov g) = fmapCov g ∘ joinCov
joinCov-fmapCov : ∀ {P Q : S.Con → Type} {X}
                (g : ∀ {Δ} → P Δ → Q Δ)
                (c : Cov (Cov P) X)
              → joinCov (fmapCov (fmapCov g) c) ≡ fmapCov g (joinCov c)
joinCov-fmapCov g (return c') = refl
joinCov-fmapCov g (abort ne) = refl
joinCov-fmapCov g (case ne c1 c2) = λ i → case ne (joinCov-fmapCov g c1 i) (joinCov-fmapCov g c2 i)

-- embCov (fmapCov f c) ≡ runTm (fmapCov (Nf-emb ∘ f) c)
embCov-fmapCov : ∀ {P : S.Con → Type} {X Aˢ} (f : ∀ {Δ} → P Δ → N.Nf Δ Aˢ) (c : Cov P X)
               → embCov (fmapCov f c) ≡ runTm (fmapCov (λ p → N.Nf-emb (f p)) c)
embCov-fmapCov f (return x) = refl
embCov-fmapCov f (abort ne) = refl
embCov-fmapCov f (case ne c1 c2) = λ i → S.caseₗ (N.Ne-emb ne) (embCov-fmapCov f c1 i) (embCov-fmapCov f c2 i)

-- c ≡ joinCov (fmapCov exfalso c) for c : Cov (λ _ → ⊥)
⊥-η-Cov : ∀ {X} (c : Cov (λ _ → ⊥) X) → c ≡ joinCov (fmapCov (λ v → exfalso v) c)
⊥-η-Cov (return v) = exfalso v
⊥-η-Cov (abort ne) = refl
⊥-η-Cov (case ne c1 c2) = λ i → case ne (⊥-η-Cov c1 i) (⊥-η-Cov c2 i)

fmapCov-exf-wkCov⊥ : ∀ {P : S.Con → Type} {X Y}
                    (wkP : ∀ {X Y} → P X → W.Wk Y X → P Y)
                    (f : ∀ {Δ} → ⊥ → P Δ)
                    (c : Cov (λ _ → ⊥) X) (x : W.Wk Y X)
                  → fmapCov f (wkCov wkP⊥ c x) ≡ wkCov wkP (fmapCov f c) x
fmapCov-exf-wkCov⊥ wkP f (return v) x = exfalso v
fmapCov-exf-wkCov⊥ wkP f (abort ne) x = refl
fmapCov-exf-wkCov⊥ wkP f (case ne c1 c2) x = λ i → case (ne N.[ x ]ᴺᵉ) (fmapCov-exf-wkCov⊥ wkP f c1 (x W.↑') i) (fmapCov-exf-wkCov⊥ wkP f c2 (x W.↑') i)

runTm-fmapCov-exf : ∀ {X Aˢ}
                   (g : ∀ {Δ} → ⊥ → S.Tm Δ Aˢ)
                   (c : Cov (λ _ → ⊥) X)
                 → runTm (fmapCov g c) ≡ S.exfalsoₗ {A = Aˢ} (runTm (fmapCov (λ v → exfalso v) c))
runTm-fmapCov-exf g (return v) = exfalso v
runTm-fmapCov-exf g (abort ne) = λ i → S.exfalsoₗ (S.⊥ₗ-η (N.Ne-emb ne) i)
runTm-fmapCov-exf g (case ne c1 c2) = (λ i → S.caseₗ (N.Ne-emb ne) (runTm-fmapCov-exf g c1 i) (runTm-fmapCov-exf g c2 i)) ∙ sym (S.π-+0 (N.Ne-emb ne) (runTm (fmapCov (λ v → exfalso v) c1)) (runTm (fmapCov (λ v → exfalso v) c2)))

mapCov-return : ∀ {P : S.Con → Type} {X} (c : Cov P X)
              → joinCov (mapCov (λ w x → return x) c) ≡ c
mapCov-return (return x) = refl
mapCov-return (abort ne) = refl
mapCov-return (case ne c1 c2) = λ i → case ne (mapCov-return c1 i) (mapCov-return c2 i)

-- fmapCov f (fmapCov g c) ≡ fmapCov (f ∘ g) c
fmapCov-∘ : ∀ {P Q R : S.Con → Type} {X}
           (f : ∀ {Δ} → Q Δ → R Δ) (g : ∀ {Δ} → P Δ → Q Δ)
           (c : Cov P X)
         → fmapCov f (fmapCov g c) ≡ fmapCov (λ x → f (g x)) c
fmapCov-∘ f g (return x) = refl
fmapCov-∘ f g (abort ne) = refl
fmapCov-∘ f g (case ne c1 c2) = λ i → case ne (fmapCov-∘ f g c1 i) (fmapCov-∘ f g c2 i)

