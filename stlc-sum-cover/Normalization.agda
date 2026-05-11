{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 
open import Agda.Primitive 
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Relation.Binary.Base 
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary 
open import Cubical.Data.Sigma hiding (_,_; Sub)
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Nat
open import Cubical.Reflection.RecordEquiv hiding (_,_)
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path hiding (_,_)
open import Cubical.Data.Equality hiding (Iso; _≡_; funExt; _∙_; assoc; refl; sym; cong; id; step-≡;_∎)

import stlc-sum-cover.Syntax as S 
open import stlc-sum-cover.InitialModel
open import stlc-sum-cover.Weakening as W  using (Wk; Wk-emb; Wk-emb-∘; Wk-emb-id; Var; Var-emb)
open import stlc-sum-cover.NormalForm as N using
    ( Ne; Nf; discreteNf; Ne-emb; Nf-emb;
      _[_]ᴺᵉ; _[_]ᴺᶠ; Ne-emb-[]; Nf-emb-[]; []ᴺᵉ-∘; []ᴺᵉ-id; []ᴺᶠ-∘; []ᴺᶠ-id)
-- twisted gluing
import stlc-sum-cover.Cover as Co
import stlc-sum-cover.DepModel as D
import stlc-sum-cover.Induction

module stlc-sum-cover.Normalization where
  private variable
    n : ℕ
    X Y Z P : S.Con
    Γˢ Δˢ : S.Con
    γˢ γ₁ˢ γ₂ˢ δˢ θˢ : S.Sub Δˢ Γˢ
    Aˢ Bˢ Cˢ Dˢ Eˢ : S.Ty
    aˢ a₁ˢ a₂ˢ bˢ cˢ fˢ tˢ : S.Tm Γˢ Aˢ

  record Con (Γˢ : S.Con) : Type₁ where
    no-eta-equality
    infixl 40 _[_]
    field
      -- Presheaf structure: [[Γ]] over Wk
      ∣_∣ : S.Con → hSet lzero                                                  -- [[Γ]]Δ
      _[_] : fst ∣ X ∣ → Wk Y X → fst ∣ Y ∣                                   -- ren τ
      ![]-∘ : ∀ γ (x : Wk Y X) (y : Wk Z Y) → γ [ x W.∘' y ] ≡ γ [ x ] [ y ] 
      ![]-id : (γ : fst ∣ X ∣) → γ [ W.id' ] ≡ γ                               

      -- gluing:  [[Γ]] →̂ Sub(−, Γ)
      map : fst ∣ X ∣ → S.Sub X Γˢ
      map-[] : ∀ γ (x : Wk Y X) → map (γ [ x ]) ≡ map γ S.∘ Wk-emb x

  open Con public renaming (_[_] to _!_[_])

  private variable Γ Δ Θ Ξ : Con Γˢ

  record Sub (Δ : Con Δˢ) (Γ : Con Γˢ) (γˢ : S.Sub Δˢ Γˢ) : Type where
    no-eta-equality
    module Δ = Con Δ
    field
      ∣_∣ :  fst  (Con.∣ Δ ∣ X)  → fst (Con.∣ Γ ∣ X)
      ![] : ∀ δ (x : Wk Y X) → ∣ (Δ ! δ [ x ]) ∣ ≡ Γ ! ∣ δ ∣ [ x ] 
      map : (δ : fst (Con.∣ Δ ∣ X)) → Γ .map ∣ δ ∣ ≡ γˢ S.∘ Δ .map δ 
    
  open Sub public

  SubΣ : ∀ {Δˢ Γˢ} (Δ : Con Δˢ) (Γ : Con Γˢ) (γˢ : S.Sub Δˢ Γˢ) → Type
  SubΣ Δ Γ γˢ =
    Σ (∀ {X} → fst (Con.∣ Δ ∣ X) → fst (Con.∣ Γ ∣ X)) λ f →
    (∀ {X Y} δ (x : Wk Y X) → f (Δ ! δ [ x ]) ≡ Γ ! (f δ) [ x ]) ×
    (∀ {X} (δ : fst (Con.∣ Δ ∣ X)) → Con.map Γ (f δ) ≡ γˢ S.∘ Con.map Δ δ)

  SubIsoΣ : ∀ {Δˢ Γˢ} (Δ : Con Δˢ) (Γ : Con Γˢ) (γˢ : S.Sub Δˢ Γˢ) → Iso (Sub Δ Γ γˢ) (SubΣ Δ Γ γˢ)
  SubIsoΣ Δ Γ γˢ = iso forward inverse right-inv left-inv
    where
      forward : Sub Δ Γ γˢ → SubΣ Δ Γ γˢ
      forward s = (Sub.∣_∣ s , Sub.![] s , Sub.map s)

      inverse : SubΣ Δ Γ γˢ → Sub Δ Γ γˢ
      inverse (s , w , m) = record { ∣_∣ = s ; ![] = w ; map = m }

      right-inv : (b : SubΣ Δ Γ γˢ) → forward (inverse b) ≡ b
      right-inv (s , w , m) = λ i → (λ x → s x) , (λ δ x → w δ x) , λ δ  → m δ

      left-inv : (a : Sub Δ Γ γˢ) → inverse (forward a) ≡ a
      ∣ left-inv a i ∣ = Sub.∣_∣ a
      left-inv a i .![] = Sub.![] a
      left-inv a i .map = Sub.map a

  isSetSub : ∀ {Δˢ Γˢ} (Δ : Con Δˢ) (Γ : Con Γˢ) (γˢ : S.Sub Δˢ Γˢ) → isSet (Sub Δ Γ γˢ)
  isSetSub Δ Γ γˢ = isOfHLevelRetractFromIso 2 (SubIsoΣ Δ Γ γˢ) isSet-SubΣ
    where
      isSet-SubΣ : isSet (SubΣ Δ Γ γˢ)
      isSet-SubΣ = isSetΣ ((isSetImplicitΠ λ X → isSetΠ λ δ → snd (Con.∣ Γ ∣ X))) λ f → isProp→isSet (isProp× (isPropImplicitΠ2 (λ X Y → isPropΠ λ δ → isPropΠ λ x → 
            snd (Con.∣ Γ ∣ Y) _ _)) (isPropImplicitΠ λ X → isPropΠ λ δ → S.SubSet _ _))

  infix 4 _≡ˢ[_]_
  _≡ˢ[_]_ : Sub Δ Γ γ₁ˢ → γ₁ˢ ≡ γ₂ˢ → Sub Δ Γ γ₂ˢ → Type 
  _≡ˢ[_]_ {Δ = Δ} {Γ = Γ} γ₁ γ₁ˢ≡γ₂ˢ γ₂ = PathP (λ i → Sub Δ Γ (γ₁ˢ≡γ₂ˢ i)) γ₁ γ₂

  Sub-path :
    {γ₁ : Sub Δ Γ γ₁ˢ} {γ₂ : Sub Δ Γ γ₂ˢ} {γ₁ˢ≡γ₂ˢ : γ₁ˢ ≡ γ₂ˢ} →
    (∀ {X} (δ : fst (Con.∣ Δ ∣ X)) →  Sub.∣ γ₁ ∣ δ ≡  Sub.∣ γ₂ ∣ δ) → γ₁ ≡ˢ[ γ₁ˢ≡γ₂ˢ ] γ₂
  ∣ Sub-path sem-path i ∣  δ = sem-path δ i
  Sub-path  {Δ = Δ} {Γ = Γ} {γ₁ = γ₁} {γ₂ = γ₂} sem-path i .![] {X} {Y} = isProp→PathP 
    {B = λ i → ∀ {Y} {X} δ (x : Wk Y X) → sem-path (Δ ! δ [ x ]) i ≡ Γ ! sem-path δ i [ x ]} (λ i₁ → isPropImplicitΠ2 λ X' Y' → isPropΠ2 λ y w → snd (∣ Γ ∣ X') _ _) 
    ( γ₁ .![]) ( γ₂ .![]) i
  Sub-path {Δ = Δ} {Γ = Γ} {γ₁ = γ₁} {γ₂ = γ₂} {γ₁ˢ≡γ₂ˢ = γ₁ˢ≡γ₂ˢ} sem-path i .map = isProp→PathP
    {B = λ i → ∀ δ → Γ .map (sem-path δ i) ≡ γ₁ˢ≡γ₂ˢ i S.∘ Δ .map δ} (λ i₁ → isPropΠ λ x → S.SubSet (map Γ (sem-path x i₁)) (γ₁ˢ≡γ₂ˢ i₁ S.∘ map Δ x)) (γ₁ .map) (γ₂ .map) i

  infixl 40 _∘_
  _∘_ : Sub Δ Γ γˢ → Sub Θ Δ δˢ → Sub Θ Γ (γˢ S.∘ δˢ)
  ∣ _∘_  γ δ ∣ x = ∣ γ ∣ (∣ δ ∣ x)
  _∘_ {Δ = Δ} {Γ = Γ} {Θ = Θ} γ δ .![] θ x = (λ i → ∣ γ ∣ (δ .![] θ x i)) ∙ γ .![] _ _
  _∘_ {Δ = Δ} {Γ = Γ} {γˢ = γˢ} {Θ = Θ} γ δ  .map θ = γ .map _  ∙ (λ i → γˢ S.∘ δ .map θ i) ∙  S.assoc _ _ _

  assoc :
    (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) (θ : Sub Ξ Θ θˢ) →
    γ ∘ (δ ∘ θ) ≡ˢ[ S.assoc _ _ _ ] γ ∘ δ ∘ θ
  assoc γ δ θ = Sub-path λ ξ → refl

  id : Sub Γ Γ S.id 
  ∣ id ∣ γ = γ
  id .![] γ x = refl
  id .map γ = sym (S.idl _)

  idr : (γ : Sub Δ Γ γˢ) → γ ∘ id ≡ˢ[ S.idr _ ] γ
  idr γ = Sub-path λ δ → refl

  idl : (γ : Sub Δ Γ γˢ) → id ∘ γ ≡ˢ[ S.idl _ ] γ
  idl γ = Sub-path λ δ → refl

  record Ty (Aˢ : S.Ty) : Type₁ where
    no-eta-equality
    infixl 40 _[_]
    field
      -- Presheaf structure: [[A]] over Wk
      ∣_∣ : S.Con → hSet lzero                                                     -- [[A]]Γ
      _[_] : fst ∣ X ∣ → Wk Y X → fst ∣ Y ∣                                         -- ren τ
      ![]-∘ : ∀ a (x : Wk Y X) (y : Wk Z Y) → a [ x W.∘' y ] ≡ (a [ x ] [ y ])    -- functoriality
      ![]-id : (a : fst ∣ X ∣) → a [ W.id' ]  ≡ a                                  -- functoriality

      -- Gluing projection: [[A]] →̂ Tm(−, A)
      map : fst ∣ X ∣ → S.Tm X Aˢ
      map-[] : ∀ a (x : Wk Y X) → map (a [ x ]) ≡ map a S.[ Wk-emb x ] -- naturality

      -- Reification ↓ᴬ : [[A]] →̂ C(Nf A)
      quo : fst ∣ X ∣ → Co.Cov (λ Δ → Nf Δ Aˢ) X
      quo-[] : ∀ a (x : Wk Y X) → quo (a [ x ]) ≡ Co.wkCov (λ nf ρ → nf [ ρ ]ᴺᶠ) (quo a) x -- naturality
      emb-quo : (a : fst ∣ X ∣) → Co.embCov (quo a) ≡ map a -- coherence: emb ∘ ↓ = map

      -- Reflection ↑ᴬ : Ne A →̂ [[A]]
      ref : Ne X Aˢ → fst ∣ X ∣
      ref-[] : ∀ a (x : Wk Y X) → ref (a [ x ]ᴺᵉ) ≡ ref a [ x ] -- naturality
      map-ref : (a : Ne X Aˢ) → map (ref a) ≡ Ne-emb a -- map ∘ ↑ = Ne-emb

      -- ⟦abort⟧ : Ne ⊥ₗ → [[A]]  (run ∘ mapC magic)
      abort-sem : ∀ {X} → Ne X S.⊥ₗ → fst ∣ X ∣
      abort-sem-[] : ∀ {X Y} (t : Ne X S.⊥ₗ) (x : Wk Y X) → abort-sem (t [ x ]ᴺᵉ) ≡ abort-sem t [ x ]
      map-exfalso : ∀ {X} (t : Ne X S.⊥ₗ) → map (abort-sem t) ≡ S.exfalsoₗ (Ne-emb t)

      -- runᴬ : C[[A]] → [[A]]
      run : ∀ {X} → Co.Cov (λ Δ → fst ∣ Δ ∣) X → fst ∣ X ∣
      run-[] : ∀ {X Y} (c : Co.Cov (λ Δ → fst ∣ Δ ∣) X) (x : Wk Y X) 
                  → run (Co.wkCov _[_] c x) ≡ run c [ x ]               -- naturality
      map-run : ∀ {X} (c : Co.Cov (λ Δ → fst ∣ Δ ∣) X) 
                   → map (run c) ≡ Co.runTm (Co.fmapCov map c)          -- coherence with map
      run-return : ∀ {X} (a : fst ∣ X ∣) → run (Co.return a) ≡ a         -- run ∘ return = id
      run-abort : ∀ {X} (ne : Ne X S.⊥ₗ) → run (Co.abort ne) ≡ abort-sem ne   -- run (abort ne) = abort-sem ne
      run-case : ∀ {X Aˢ' Bˢ'} (ne : Ne X (Aˢ' S.+ Bˢ'))  
                        (c1 : Co.Cov (λ Δ → fst ∣ Δ ∣) (X S.▸ Aˢ'))
                        (c2 : Co.Cov (λ Δ → fst ∣ Δ ∣) (X S.▸ Bˢ'))
                      → run (Co.case ne c1 c2) ≡ run (Co.case ne (Co.return (run c1)) (Co.return (run c2)))

  open Ty public renaming (_[_] to _!_[_])
  private variable A B C : Ty Aˢ
  
  record Tm (Γ : Con Γˢ) (A : Ty Aˢ) (aˢ : S.Tm Γˢ Aˢ) : Type where
    no-eta-equality
    module Γ = Con Γ
    field
      ∣_∣ : fst (Con.∣ Γ ∣ X)  → fst (Ty.∣ A ∣ X) 
      ![] : ∀ γ (x : Wk Y X) → ∣ (Γ ! γ [ x ]) ∣ ≡ A ! ∣ γ ∣ [ x ]
      map : (γ : fst (Con.∣ Γ ∣ X)) →  A .map ∣ γ ∣ ≡ aˢ S.[ Γ .map γ ]

  open Tm public
  TmΣ : ∀ {Γˢ Aˢ} (Γ : Con Γˢ) (A : Ty Aˢ) (aˢ : S.Tm Γˢ Aˢ) → Type
  TmΣ Γ A aˢ =
    Σ (∀ {X} → fst (Con.∣ Γ ∣ X) → fst (Ty.∣ A ∣ X)) λ f →
    (∀ {X Y} γ (x : Wk Y X) → f (Γ ! γ [ x ]) ≡ A ! (f γ) [ x ]) ×
    (∀ {X} (γ : fst (Con.∣ Γ ∣ X)) → Ty.map A (f γ) ≡ aˢ S.[ Con.map Γ γ ])

  TmIsoΣ : ∀ {Γˢ Aˢ} (Γ : Con Γˢ) (A : Ty Aˢ) (aˢ : S.Tm Γˢ Aˢ) → Iso (Tm Γ A aˢ) (TmΣ Γ A aˢ)
  TmIsoΣ Γ A aˢ = iso forward inverse right-inv left-inv
    where
      forward : Tm Γ A aˢ → TmΣ Γ A aˢ
      forward t = (Tm.∣_∣ t) , Tm.![] t , Tm.map t

      inverse : TmΣ Γ A aˢ → Tm Γ A aˢ
      inverse (s , w , m) = record
        { ∣_∣ = s
        ; ![] = w
        ; map = m
        }

      right-inv : (b : TmΣ Γ A aˢ) → forward (inverse b) ≡ b
      right-inv (s , w , m) = λ i → (λ x → s x) , (λ δ x → w δ x) , λ δ  → m δ

      left-inv : (a : Tm Γ A aˢ) → inverse (forward a) ≡ a 
      ∣ left-inv a i ∣ = Tm.∣_∣ a
      left-inv a i .![] = λ γ x → Tm.![] a γ x
      left-inv a i .map = λ γ → Tm.map a γ

  isSetTm : ∀ {Γˢ Aˢ} (Γ : Con Γˢ) (A : Ty Aˢ) (aˢ : S.Tm Γˢ Aˢ) → isSet (Tm Γ A aˢ)
  isSetTm Γ A aˢ = isOfHLevelRetractFromIso 2 (TmIsoΣ Γ A aˢ) isSet-TmΣ
    where
      isSet-TmΣ : isSet (TmΣ Γ A aˢ)
      isSet-TmΣ =  isSetΣ (isSetImplicitΠ (λ X → isSetΠ λ γ → snd (Ty.∣ A ∣ X))) λ f → isProp→isSet (isProp× (isPropImplicitΠ2 (λ X Y → isPropΠ λ γ → isPropΠ λ x → snd (Ty.∣ A ∣ Y) _ _)) (isPropImplicitΠ (λ X → isPropΠ λ γ → S.TmSet _ _)))
  
  infix 4 _≡ᵗ[_]_
  _≡ᵗ[_]_ : ∀ {Γ A} → Tm Γ A a₁ˢ → a₁ˢ ≡ a₂ˢ → Tm Γ A a₂ˢ → Type
  _≡ᵗ[_]_ {Γ = Γ} {A = A} a₁ a₁ˢ≡a₂ˢ a₂ =
    PathP (λ i → Tm Γ A (a₁ˢ≡a₂ˢ i)) a₁ a₂

  
  Tm-path :
    {a₁ : Tm Γ A a₁ˢ} {a₂ : Tm Γ A a₂ˢ} {a₁ˢ≡a₂ˢ : a₁ˢ ≡ a₂ˢ} →
    (∀ {X} (γ : fst (Con.∣ Γ ∣ X) ) → ∣ a₁ ∣ γ ≡ ∣ a₂ ∣ γ) → a₁ ≡ᵗ[ a₁ˢ≡a₂ˢ ] a₂
  ∣ Tm-path {a₁ = a₁} {a₂ = a₂} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} path i ∣ = λ x → path x i 
  Tm-path {Γ = Γ}  {A = A} {a₁ = a₁} {a₂ = a₂} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ}  path i .![] {X} {Y} γ x = isProp→PathP {B = λ i → path (Γ ! γ [ x ]) i ≡ A ! path γ i [ x ] } (λ i₁ → (snd (∣ A ∣ X) ) _ _ ) (a₁ .![] γ x) (a₂ .![] γ x) i
  Tm-path {Γ = Γ} {A = A} {a₁ = a₁} {a₂ = a₂} {a₁ˢ≡a₂ˢ = a₁ˢ≡a₂ˢ} path i .map γ = isProp→PathP {B = λ i → A .map (path γ i) ≡ (a₁ˢ≡a₂ˢ i S.[ map Γ γ ])}  (λ i₁ → S.TmSet _ _)  (a₁ .map γ) (a₂ .map γ ) i 
  
  _[_] : Tm Γ A aˢ → Sub Δ Γ γˢ → Tm Δ A (aˢ S.[ γˢ ])
  ∣ _[_] a γ ∣ δ = ∣  a ∣ (∣ γ ∣ δ)
  _[_] {Γ = Γ} {A = A} {Δ = Δ} a γ .![] δ x  = (λ i → ∣ a ∣  ((γ .![] δ x) i)) ∙ a .![] _ _
  _[_] {Γ = Γ} {A = A} {aˢ = aˢ} {Δ = Δ} {γˢ = γˢ} a γ  .map  δ = a .map _ ∙ (λ i → aˢ S.[  γ .map δ i ]) ∙  S.[]-∘ _ _ _

  []-∘ :
    (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) (δ : Sub Θ Δ δˢ) →
    a [ γ ∘ δ ] ≡ᵗ[ S.[]-∘ _ _ _ ] a [ γ ] [ δ ]
  []-∘ a γ δ = Tm-path λ θ → refl

  []-id : (a : Tm Γ A aˢ) → a [ id ] ≡ᵗ[ S.[]-id _ ] a
  []-id a = Tm-path λ γ → refl

  infixl 4 _▸_
  _▸_ : Con Γˢ → Ty Aˢ → Con (Γˢ S.▸ Aˢ)
  ∣ Γ ▸ A ∣ X = fst( ∣ Γ ∣ X) × fst(∣ A ∣ X) , isSet× (snd( ∣ Γ ∣ X)) (snd( ∣ A ∣ X))
  (Γ ▸ A) ! (γ , a) [ x ] = Γ ! γ [ x ] , A ! a [ x ]
  (Γ ▸ A) .![]-∘ (γ , a) x y = ΣPathP (Γ .![]-∘ γ x y , A .![]-∘ a x y)
  (Γ ▸ A) .![]-id (γ , a) = ΣPathP (Γ .![]-id γ , A .![]-id a)
  (Γ ▸ A) .map (γ , a) = Γ .map γ S., A .map a
  (Γ ▸ A) .map-[] (γ , a) x = ((λ i → Γ .map-[] γ x i S., A .map (A ! a [ x ])) ∙ λ i → map Γ γ S.∘ Wk-emb x S., A .map-[] a x i) ∙  sym (S.,-∘ _ _ _) 

  p : Sub (Γ ▸ A) Γ S.p
  ∣ p ∣ = fst
  p .![] (γ , a) x = refl
  p .map (γ , a) = sym (S.▸-β₁ _ _)

  q : Tm (Γ ▸ A) A S.q
  ∣ q ∣ = snd
  q .![] (γ , a) x = refl
  q .map (γ , a) = sym (S.▸-β₂ _ _)

  infixl 4 _,_ₛ
  _,_ₛ : Sub Δ Γ γˢ → Tm Δ A aˢ → Sub Δ (Γ ▸ A) (γˢ S., aˢ)
  ∣ γ , a ₛ ∣ δ = ∣ γ ∣ δ ,  ∣ a ∣ δ 
  (γ , a ₛ) .![] δ x = ΣPathP (γ .![] δ x , a .![] δ x)
  _,_ₛ {Δ = Δ} {Γ = Γ} {γˢ = γˢ} {A = A} {aˢ = aˢ} γ a .map δ = (λ i → (γ .map δ i) S., A .map (∣ a ∣ δ)) ∙ (λ i → (γˢ S.∘ map Δ δ S., a .map δ i)) ∙ sym (S.,-∘ _ _ _)

  ,-∘ :
    (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) (δ : Sub Θ Δ δˢ) →
    (γ , a ₛ) ∘ δ ≡ˢ[ S.,-∘ _ _ _ ] (γ ∘ δ , a [ δ ] ₛ)
  ,-∘ γ a δ = Sub-path λ θ → refl

  ▸-β₁ :
    ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
    p ∘ (γ , a ₛ) ≡ˢ[ S.▸-β₁ _ _ ] γ
  ▸-β₁ γ a = Sub-path λ δ → refl

  ▸-β₂ :
    ∀ {Γ Δ A} (γ : Sub Δ Γ γˢ) (a : Tm Δ A aˢ) →
    q [ γ , a ₛ ] ≡ᵗ[ S.▸-β₂ _ _ ] a
  ▸-β₂ γ a = Tm-path λ δ → refl

  ▸-η : (p , q ₛ) ≡ˢ[ S.▸-η ] id {Γ = Γ ▸ A}
  ▸-η = Sub-path λ (γ , a) → refl

  ◆ : Con S.◆
  ∣ ◆ ∣ = λ x → Unit , (λ _ _ _ _ _ _ → tt)
  ◆ ._!_[_] tt x = tt
  ◆ .![]-∘ tt x y =  refl
  ◆ .![]-id tt = refl
  ◆ .map tt = S.ε
  ◆ .map-[] tt x = sym (S.ε-∘ _)

  ε : Sub Γ ◆ S.ε
  ∣ ε ∣ γ = tt
  ε .![] γ x = refl
  ε .map γ = sym (S.ε-∘ _) 

  ε-∘ : (γ : Sub Δ Γ γˢ) → ε ∘ γ ≡ˢ[ S.ε-∘ _ ] ε
  ε-∘ γ = Sub-path λ δ → refl

  ◆-η : ε ≡ˢ[ S.◆-η ] id
  ◆-η = Sub-path λ _ → refl

  infixl 4 _↑
  _↑ : Sub Δ Γ γˢ → Sub (Δ ▸ A) (Γ ▸ A) (γˢ S.↑)
  γ ↑ = γ ∘ p , q ₛ

  ⟨_⟩ : Tm Γ A aˢ → Sub Γ (Γ ▸ A) S.⟨ aˢ ⟩
  ⟨_⟩ = λ x → id , x ₛ
  
  record Fun (X : S.Con) (A : Ty Aˢ) (B : Ty Bˢ) : Type where
    no-eta-equality
    module A = Ty A
    field
      syn : S.Tm X (Aˢ S.⇒ Bˢ)
      sem  : Wk Y X → fst (∣ A ∣ Y) → fst (∣ B ∣ Y) 
      ![] : ∀ (x : Wk Y X) a (y : Wk Z Y) → sem (x W.∘' y) (A ! a [ y ]) ≡ B ! sem x a [ y ] 
      map : ∀ (x : Wk Y X) a → B .map (sem x a) ≡ S.app (syn S.[ Wk-emb x ]) (A .map a)

  open Fun public
  FunΣ : (X : S.Con) {Aˢ Bˢ : S.Ty} (A : Ty Aˢ) (B : Ty Bˢ) → Type
  FunΣ X {Aˢ} {Bˢ} A B =
    Σ (S.Tm X (Aˢ S.⇒ Bˢ)) λ syn →
    Σ (∀ {Y} → Wk Y X → fst (∣ A ∣ Y) → fst (∣ B ∣ Y)) λ sem →
    (∀ {Y Z} (x : Wk Y X) (a : fst (∣ A ∣ Y)) (y : Wk Z Y) → sem (x W.∘' y) (A ! a [ y ]) ≡ B ! sem x a [ y ]) ×
    (∀ {Y} (x : Wk Y X) (a : fst (∣ A ∣ Y)) → B .map (sem x a) ≡ S.app (syn S.[ Wk-emb x ]) (A .map a))
    
  FunIsoΣ : (X : S.Con) {Aˢ Bˢ : S.Ty} (A : Ty Aˢ) (B : Ty Bˢ) → Iso (Fun X A B) (FunΣ X A B)
  FunIsoΣ X A B = iso forward inverse right-inv left-inv
    where
      forward : Fun X A B → FunΣ X A B
      forward f = f .syn , f .sem , f .![] , f .map

      inverse : FunΣ X A B → Fun X A B
      inverse (s , m , w , p) = record
        { syn = s
        ; sem = m
        ; ![] = w
        ; map = p
        }

      right-inv : (b : FunΣ X A B) → forward (inverse b) ≡ b
      right-inv (s , m , w , p) = refl

      left-inv : (a : Fun X A B) → inverse (forward a) ≡ a
      left-inv a i .syn = a .syn
      left-inv a i .sem = a .sem
      left-inv a i .![] = a .![]
      left-inv a i .map = a .map

  Fun-is-set : isSet (Fun X A B)
  Fun-is-set {X = X} {A = A} {B = B} = isOfHLevelRetractFromIso 2 (FunIsoΣ X A B) isSet-FunΣ
    where
      isSet-FunΣ : isSet (FunΣ X A B)
      isSet-FunΣ = isSetΣ S.TmSet (λ f → isSetΣ (isSetImplicitΠ λ Y → isSetΠ (λ x → isSet→ (snd (∣ B ∣ Y)))) λ m → isProp→isSet (isProp× (isPropImplicitΠ2 (λ Y Z → isPropΠ λ a → isPropΠ2 λ y z → snd (∣ B ∣ Z) _ _)) (isPropImplicitΠ λ Y → isPropΠ λ x → isPropΠ λ a → S.TmSet _ _))) 
  
  Fun-path : ∀ {f₁ f₂ : Fun X A B} → 
    f₁ .syn ≡ f₂ .syn → 
    (∀ {Y} (x : Wk Y X)(a : fst (∣ A ∣ Y)) → f₁ .sem x a ≡ f₂ .sem x a) 
    → f₁ ≡ f₂ 
  Fun-path syn-path sem-path i .syn = syn-path i
  Fun-path syn-path sem-path i .sem x a = sem-path x a i
  Fun-path {X = X} {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .![] = isProp→PathP {B = λ i → ∀ {Z} {Y} (x : Wk Y X) a (y : Wk Z Y) → sem-path (x W.∘' y) (A ! a [ y ]) i ≡ B ! sem-path x a i [ y ]} (λ i₁ → isPropImplicitΠ2 λ X' Y' → isPropΠ3 λ w y' w' → snd (∣ B ∣ X') _ _) (f₁ .![]) (f₂ .![]) i
  Fun-path {X = X} {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .map = isProp→PathP {B = λ i → ∀ {Y} (x : Wk Y X) a →  map B (sem-path x a i) ≡  S.app (syn-path i S.[ Wk-emb x ]) (map A a)} (λ i₁ → isPropImplicitΠ λ Y → isPropΠ2 λ w y → S.TmSet _ _) (f₁ .map) (f₂ .map) i

  infixr 0 _⇒_

  appCov : ∀ {X Aˢ Bˢ} {A : Ty Aˢ} {B : Ty Bˢ} → Co.Cov (λ Δ → Fun Δ A B) X → fst (Ty.∣ A ∣ X) → fst (Ty.∣ B ∣ X)
  appCov (Co.return fv) a = fv .sem W.id' a
  appCov {B = B} (Co.abort ne) a = B .abort-sem ne
  appCov {A = A} {B = B} (Co.case ne c1 c2) a = 
    B .run (Co.case ne (Co.return (appCov c1 (A ! a [ W.id' W.∘p ]))) 
                            (Co.return (appCov c2 (A ! a [ W.id' W.∘p ]))))

  isSetCov : ∀ {P : S.Con → Type} {Γ} → isSet (P Γ) → isSet (Co.Cov P Γ)
  isSetCov isSetP = {!   !} 
  
  {-# TERMINATING #-}
  _⇒_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.⇒ Bˢ)
  ∣ A ⇒ B ∣ X = Fun X A B , Fun-is-set

  ((A ⇒ B) ! f [ x ]) .syn = f .syn S.[ Wk-emb x ]
  ((A ⇒ B) ! f [ x ]) .sem = λ y a → f .sem (x W.∘' y) a
  ((A ⇒ B) ! f [ x ]) .![] = λ y a z → (λ i → f .sem (W.assoc' x y z i) (A ! a [ z ])) ∙ f .![] (x W.∘' y) a z
  ((A ⇒ B) ! f [ x ]) .map = λ y a → f .map (x W.∘' y) a 
                  ∙ (λ i → S.app (f .syn S.[ Wk-emb-∘ x y i ]) (A .map a)) 
                  ∙ (λ i → S.app (S.[]-∘ (f .syn) (Wk-emb x) (Wk-emb y) i) (A .map a))
  (A ⇒ B) .![]-∘ f x y = Fun-path ((λ i → f .syn S.[ Wk-emb-∘ x y i ]) ∙ S.[]-∘ _ _ _) 
                                  (λ z a i → f .sem (sym (W.assoc' x y z) i) a)
  (A ⇒ B) .![]-id f = Fun-path ((λ i → f .syn S.[ Wk-emb-id i ]) ∙ S.[]-id _) 
                               (λ x a i → f .sem (W.idl' x i) a)
  (A ⇒ B) .map f = f .syn
  (A ⇒ B) .map-[] f x = refl

  (A ⇒ B) .quo f = Co.return (Co.collapseNf (B .quo (f .sem (W.id' W.∘p) (A .ref (N.var W.q)))))
  (A ⇒ B) .quo-[] f x = cong Co.return 
    ((λ i → Co.collapseNf (B .quo (f .sem (Co.wk-comm x i) ((A .ref-[] (N.var W.q) (x W.↑')  i)))))
    ∙ (λ i → Co.collapseNf (B .quo (f .![] (W.id' W.∘p) (A .ref (N.var W.q)) (x W.↑') i )))
    ∙ (λ i → Co.collapseNf (B .quo-[] (f .sem (W.id' W.∘p) (A .ref (N.var W.q))) (x W.↑') i))
    ∙ Co.collapseNf-[] (B .quo (f .sem (W.id' W.∘p) (A .ref (N.var W.q)))) x )  
  (A ⇒ B) .emb-quo f = Co.emb-collapseNf (B .quo (f .sem (W.id' W.∘p) (A .ref (N.var W.q))))
    ∙ (λ i → S.lam (B .emb-quo (f .sem (W.id' W.∘p) (A .ref (N.var W.q))) i))
    ∙ (λ i → S.lam (f .map (W.id' W.∘p) (A .ref (N.var W.q)) i))
    ∙ (λ i → S.lam (S.app (f .syn S.[ Co.wk-p-eq i ]) (A .map (A .ref (N.var W.q)))))
    ∙ (λ i → S.lam (S.app (f .syn S.[ S.p ]) (A .map-ref (N.var W.q) i)))
    ∙ S.⇒-η (f .syn)


  (A ⇒ B) .ref f .syn = Ne-emb f
  (A ⇒ B) .ref f .sem = λ x a → B .ref (N.app (f [ x ]ᴺᵉ) (Co.runNf (A .quo a)))
  (A ⇒ B) .ref f .![] = λ x a y → (λ i → ref B (Ne.app ([]ᴺᵉ-∘ f x y i) (Co.runNf (quo A (A ! a [ y ])))))
                     ∙ (λ i → ref B (Ne.app (f [ x ]ᴺᵉ [ y ]ᴺᵉ) (Co.runNf (A .quo-[] a y i))))
                     ∙ (λ i → ref B (Ne.app (f [ x ]ᴺᵉ [ y ]ᴺᵉ) (Co.runNf-[] (A .quo a) y i)))
                     ∙ B .ref-[] _ _
  (A ⇒ B) .ref f .map = λ x a → B .map-ref (Ne.app (f [ x ]ᴺᵉ) (Co.runNf (quo A a)))
                   ∙ (λ i → S.app (Ne-emb-[] f x i) (Nf-emb (Co.runNf (A .quo a))))
                   ∙ (λ i → S.app (Ne-emb f S.[ Wk-emb x ]) (Co.emb-runNf (A .quo a) i))
                   ∙ (λ i → S.app (Ne-emb f S.[ Wk-emb x ]) (A .emb-quo a i))
  (A ⇒ B) .ref-[] f x = Fun-path (Ne-emb-[] f x) (λ y a i → ref B (Ne.app ([]ᴺᵉ-∘ f x y (~ i)) (Co.runNf (quo A a))))
  (A ⇒ B) .map-ref f = refl


  (A ⇒ B) .abort-sem t .syn = S.exfalsoₗ (Ne-emb t)
  (A ⇒ B) .abort-sem t .sem = λ x a → B .abort-sem (t [ x ]ᴺᵉ)
  (A ⇒ B) .abort-sem t .![] = λ x a y → (λ i → B .abort-sem ([]ᴺᵉ-∘ t x y i)) ∙ B .abort-sem-[] (t [ x ]ᴺᵉ) y
  (A ⇒ B) .abort-sem t .map = λ x a → B .map-exfalso (t [ x ]ᴺᵉ) 
                  ∙ (λ i → S.exfalsoₗ (Ne-emb-[] t x i))
                  ∙ sym (S.π-⇒0 (Ne-emb t S.[ Wk-emb x ]) (A .map a))
                  ∙ (λ i → S.app (sym (S.exfalsoₗ-[] (Ne-emb t) (Wk-emb x)) i) (A .map a))
  (A ⇒ B) .abort-sem-[] t x = Fun-path 
    ((λ i → S.exfalsoₗ (Ne-emb-[] t x i)) ∙ sym (S.exfalsoₗ-[] (Ne-emb t) (Wk-emb x))) 
    (λ y a i → B .abort-sem ([]ᴺᵉ-∘ t x y (~ i)))
  (A ⇒ B) .map-exfalso t = refl

  (A ⇒ B) .run c .syn = Co.runTm (Co.fmapCov (λ f → f .syn) c)
  (A ⇒ B) .run c .sem = λ x a → B .run (Co.mapCov (λ w f → f .sem W.id' (A ! a [ w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c x))
  (A ⇒ B) .run (Co.return f) .![] = λ x a y → 
    B .run-return _
    ∙ (λ i → f .sem (W.idr' (x W.∘' y) i) (A .![]-id (A ! a [ y ]) i))
    ∙ f .![] x a y
    ∙ (λ i → B ! f .sem (W.idr' x (~ i)) (A .![]-id a (~ i)) [ y ])
    ∙ cong (λ v → B ! v [ y ]) (sym (B .run-return _))
  (A ⇒ B) .run (Co.abort ne) .![] = λ x a y → 
    B .run-abort _
    ∙ (λ i → B .abort-sem (N.[]ᴺᵉ-∘ ne x y i))
    ∙ B .abort-sem-[] (ne N.[ x ]ᴺᵉ) y
    ∙ cong (λ v → B ! v [ y ]) (sym (B .run-abort _))
  (A ⇒ B) .run (Co.case {A = A₁} {B = B₁} ne c1 c2) .![] = λ x a y → 
    let idAY : W.Wk (_ S.▸ A₁) _
        idAY = W._∘p W.id'
        idBY : W.Wk (_ S.▸ B₁) _
        idBY = W._∘p W.id'
        idAZ : W.Wk (_ S.▸ A₁) _
        idAZ = W._∘p W.id'
        idBZ : W.Wk (_ S.▸ B₁) _
        idBZ = W._∘p W.id'
        xA = W._↑' {A = A₁} x
        xB = W._↑' {A = B₁} x
        yA = W._↑' {A = A₁} y
        yB = W._↑' {A = B₁} y
        xyA = W._↑' {A = A₁} (x W.∘' y)
        xyB = W._↑' {A = B₁} (x W.∘' y)
        
        a-wk-A₁ : ∀ {Δ} (w : W.Wk Δ _) → 
                 (A ! (A ! a [ y ]) [ idAZ W.∘' w ]) 
                 ≡ 
                 (A ! (A ! (A ! a [ idAY ]) [ yA ]) [ w ])
        a-wk-A₁ w = 
            sym (A .![]-∘ a y (idAZ W.∘' w))
          ∙ (λ j → A ! a [ W.assoc' y idAZ w j ])
          ∙ (λ j → A ! a [ (Co.wk-comm {A = A₁} y j) W.∘' w ])
          ∙ (λ j → A ! a [ W.assoc' idAY yA w (~ j) ])
          ∙ A .![]-∘ a idAY (yA W.∘' w)
          ∙ A .![]-∘ (A ! a [ idAY ]) yA w

        a-wk-B₁ : ∀ {Δ} (w : W.Wk Δ _) → 
                 (A ! (A ! a [ y ]) [ idBZ W.∘' w ]) 
                 ≡ 
                 (A ! (A ! (A ! a [ idBY ]) [ yB ]) [ w ])
        a-wk-B₁ w = 
            sym (A .![]-∘ a y (idBZ W.∘' w))
          ∙ (λ j → A ! a [ W.assoc' y idBZ w j ])
          ∙ (λ j → A ! a [ (Co.wk-comm {A = B₁} y j) W.∘' w ])
          ∙ (λ j → A ! a [ W.assoc' idBY yB w (~ j) ])
          ∙ A .![]-∘ a idBY (yB W.∘' w)
          ∙ A .![]-∘ (A ! a [ idBY ]) yB w

    in B .run-case (ne N.[ x W.∘' y ]ᴺᵉ)
         (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! (A ! a [ y ]) [ idAZ W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c1 xyA))
         (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! (A ! a [ y ]) [ idBZ W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c2 xyB))
    ∙ (λ i → B .run (Co.case (ne N.[ x W.∘' y ]ᴺᵉ)
               (Co.return (B .run (Co.mapCov (λ {Δ} w f → f .sem W.id' (a-wk-A₁ w i)) (Co.wkCov (_!_[_] (A ⇒ B)) c1 xyA))))
               (Co.return (B .run (Co.mapCov (λ {Δ} w f → f .sem W.id' (a-wk-B₁ w i)) (Co.wkCov (_!_[_] (A ⇒ B)) c2 xyB))))))
    ∙ (λ i → B .run (Co.case (ne N.[ x W.∘' y ]ᴺᵉ)
               (Co.return ((((A ⇒ B) .run c1) .![] xA (A ! a [ idAY ]) yA i)))
               (Co.return ((((A ⇒ B) .run c2) .![] xB (A ! a [ idBY ]) yB i)))))
    ∙ (λ i → B .run (Co.case (N.[]ᴺᵉ-∘ ne x y i)
               (Co.return (B ! (B .run (Co.mapCov (λ {Δ} w f → f .sem W.id' (A .![]-∘ a idAY w (~ i))) (Co.wkCov (_!_[_] (A ⇒ B)) c1 xA))) [ yA ]))
               (Co.return (B ! (B .run (Co.mapCov (λ {Δ} w f → f .sem W.id' (A .![]-∘ a idBY w (~ i))) (Co.wkCov (_!_[_] (A ⇒ B)) c2 xB))) [ yB ]))))
    ∙ (λ i → B .run (Co.case (ne N.[ x ]ᴺᵉ N.[ y ]ᴺᵉ)
               (Co.return (B .run-[] (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ idAY W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c1 xA)) yA (~ i)))
               (Co.return (B .run-[] (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ idBY W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c2 xB)) yB (~ i)))))
    ∙ sym (B .run-case (ne N.[ x ]ᴺᵉ N.[ y ]ᴺᵉ)
            (Co.wkCov (_!_[_] B) (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ idAY W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c1 xA)) yA)
            (Co.wkCov (_!_[_] B) (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ idBY W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c2 xB)) yB))
    ∙ B .run-[] (Co.case (ne N.[ x ]ᴺᵉ)
        (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ idAY W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c1 xA))
        (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ idBY W.∘' w ])) (Co.wkCov (_!_[_] (A ⇒ B)) c2 xB))) y
  
  (A ⇒ B) .run (Co.return f) .map = λ x a → 
    B .map-run (Co.return (f .sem (x W.∘' W.id') (A ! a [ W.id' ])))
    ∙ f .map (x W.∘' W.id') (A ! a [ W.id' ])
    ∙ (λ i → S.app (f .syn S.[ Wk-emb (W.idr' x i) ]) (A .map (A .![]-id a i)))
  (A ⇒ B) .run (Co.abort ne) .map = λ x a → 
    B .map-run (Co.abort (ne N.[ x ]ᴺᵉ))
    ∙ (λ i → S.exfalsoₗ (N.Ne-emb-[] ne x i))
    ∙ sym (S.π-⇒0 (N.Ne-emb ne S.[ Wk-emb x ]) (A .map a))
    ∙ (λ i → S.app (sym (S.exfalsoₗ-[] (N.Ne-emb ne) (Wk-emb x)) i) (A .map a))
  (A ⇒ B) .run (Co.case {A = A₁} {B = B₁} ne c1 c2) .map = λ x a → 
    let idA = W._∘p {A = A₁} W.id'
        idB = W._∘p {A = B₁} W.id'
        xA = W._↑' {A = A₁} x
        xB = W._↑' {A = B₁} x
    in B .map-run (Co.case (ne N.[ x ]ᴺᵉ)
      (Co.mapCov (λ w f → f .sem W.id' (A ! a [ idA W.∘' w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c1 xA))
      (Co.mapCov (λ w f → f .sem W.id' (A ! a [ idB W.∘' w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c2 xB)))
    ∙ (λ i → S.caseₗ (N.Ne-emb (ne N.[ x ]ᴺᵉ))
        (sym (B .map-run (Co.mapCov (λ w f → f .sem W.id' (A ! a [ idA W.∘' w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c1 xA))) i)
        (sym (B .map-run (Co.mapCov (λ w f → f .sem W.id' (A ! a [ idB W.∘' w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c2 xB))) i))
    ∙ (λ i → S.caseₗ (N.Ne-emb (ne N.[ x ]ᴺᵉ))
        (B .map (B .run (Co.mapCov (λ w f → f .sem W.id' (A .![]-∘ a idA w i)) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c1 xA))))
        (B .map (B .run (Co.mapCov (λ w f → f .sem W.id' (A .![]-∘ a idB w i)) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c2 xB)))))
    ∙ (λ i → S.caseₗ (N.Ne-emb (ne N.[ x ]ᴺᵉ))
        (((A ⇒ B) .run c1) .map xA (A ! a [ idA ]) i)
        ((((A ⇒ B) .run c2) .map xB (A ! a [ idB ]) i)))
    ∙ (λ i → S.caseₗ (N.Ne-emb (ne N.[ x ]ᴺᵉ))
        (S.app (Co.runTm (Co.fmapCov (λ f → f .syn) c1) S.[ W.Wk-emb xA ]) ((A .map-[] a idA ∙ (λ j → A .map a S.[ Co.wk-p-eq {A = A₁} j ])) i))
        (S.app (Co.runTm (Co.fmapCov (λ f → f .syn) c2) S.[ W.Wk-emb xB ]) ((A .map-[] a idB ∙ (λ j → A .map a S.[ Co.wk-p-eq {A = B₁} j ])) i)))
    ∙ (λ i → S.caseₗ (N.Ne-emb-[] ne x i)
        (S.app (Co.runTm (Co.fmapCov (λ f → f .syn) c1) S.[ W.Wk-emb x S.↑ ]) (A .map a S.[ S.p {A = A₁} ]))
        (S.app (Co.runTm (Co.fmapCov (λ f → f .syn) c2) S.[ W.Wk-emb x S.↑ ]) (A .map a S.[ S.p {A = B₁} ])))
    ∙ sym (S.π-+⇒ (N.Ne-emb ne S.[ W.Wk-emb x ]) 
            (Co.runTm (Co.fmapCov (λ f → f .syn) c1) S.[ W.Wk-emb x S.↑ ]) 
            (Co.runTm (Co.fmapCov (λ f → f .syn) c2) S.[ W.Wk-emb x S.↑ ]) 
            (A .map a))
    ∙ (λ i → S.app (sym (S.caseₗ-[] (N.Ne-emb ne) (Co.runTm (Co.fmapCov (λ f → f .syn) c1)) (Co.runTm (Co.fmapCov (λ f → f .syn) c2)) (W.Wk-emb x)) i) (A .map a))

  (A ⇒ B) .run-[] c x = Fun-path 
    (Co.runTm-fmapCov-wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) (λ f → f .syn) (λ f w' → refl) c x)
    (λ y a → cong (λ d → B .run (Co.mapCov (λ w f → f .sem W.id' (A ! a [ w ])) d)) 
      (sym (Co.wkCov-∘ (λ f w' → (A ⇒ B) ! f [ w' ]) (λ f w₁ w₂ → (A ⇒ B) .![]-∘ f w₁ w₂) c x y)))
  (A ⇒ B) .map-run c = refl
  (A ⇒ B) .run-return f = Fun-path refl 
    (λ x a → B .run-return (f .sem (x W.∘' W.id') (A ! a [ W.id' ])) 
           ∙ (λ i → f .sem (W.idr' x i) (A .![]-id a i)))
  (A ⇒ B) .run-abort ne = Fun-path refl 
    (λ x a → B .run-abort (ne N.[ x ]ᴺᵉ))
  (A ⇒ B) .run-case {Aˢ' = A₁} {Bˢ' = B₁} ne c1 c2 = Fun-path refl (λ {Y} x a → 
    let a-wk : ∀ {A'} {Δ} (w : W.Wk Δ (Y S.▸ A')) → A ! a [ (W.id' W.∘p ) W.∘' w ] ≡ A ! (A ! a [ (W.id' W.∘p ) W.∘' W.id' ]) [ w ]
        a-wk {A'} w = 
            (λ j → A ! a [ (W.id' W.∘p ) W.∘' W.idl' w (~ j) ])
          ∙ (λ j → A ! a [ W.assoc' (W.id' W.∘p) W.id' w j ])
          ∙ A .![]-∘ a ((W.id' W.∘p ) W.∘' W.id') w
    in B .run-case (ne N.[ x ]ᴺᵉ)
         (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ (W.id' W.∘p ) W.∘' w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c1 (W._↑' {A = A₁} x)))
         (Co.mapCov (λ {Δ} w f → f .sem W.id' (A ! a [ (W.id' W.∘p ) W.∘' w ])) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c2 (W._↑' {A = B₁} x)))
    ∙ (λ i → B .run (Co.case (ne N.[ x ]ᴺᵉ)
        (Co.return (B .run (Co.mapCov (λ {Δ} w f → f .sem W.id' (a-wk {A₁} w i)) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c1 (W.idr' (W._↑' {A = A₁} x) (~ i))))))
        (Co.return (B .run (Co.mapCov (λ {Δ} w f → f .sem W.id' (a-wk {B₁} w i)) (Co.wkCov (λ f w' → (A ⇒ B) ! f [ w' ]) c2 (W.idr' (W._↑' {A = B₁} x) (~ i)))))))))
  
  app : Tm Γ (A ⇒ B) fˢ → Tm Γ A aˢ → Tm Γ B (S.app fˢ aˢ)
  ∣ app {A = A} {B = B} f a ∣ γ = ∣ f ∣ γ .sem W.id' (∣ a ∣ γ)
  app {Γ = Γ} {A = A} {B = B} f a .![] γ x = 
      (λ i → f .![] γ x i .sem W.id' (a .![] γ x i))
    ∙ (λ i → ∣ f ∣ γ .sem (W.idr' x i) (A ! ∣ a ∣ γ [ x ]))
    ∙ (λ i → ∣ f ∣ γ .sem (W.idl' x (~ i)) (A ! ∣ a ∣ γ [ x ]))
    ∙ ∣ f ∣ γ .![] W.id' (∣ a ∣ γ) x
  app {Γ = Γ} {A = A} {B = B} {fˢ = fˢ} {aˢ = aˢ} f a .map γ = 
      (∣ f ∣ γ .map W.id' (∣ a ∣ γ))
    ∙ (λ i → S.app (∣ f ∣ γ .syn S.[ Wk-emb-id i ]) (A .map (∣ a ∣ γ)))
    ∙ (λ i → S.app (S.[]-id (∣ f ∣ γ .syn) i) (A .map (∣ a ∣ γ)))
    ∙ (λ i → S.app (f .map γ i) ((a .map γ) i))
    ∙ sym (S.app-[] fˢ aˢ (map Γ γ))

  app-[] :
    (f : Tm Γ (A ⇒ B) fˢ) (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) →
    app f a [ γ ] ≡ᵗ[ S.app-[] _ _ _ ] app (f [ γ ]) (a [ γ ])
  app-[] {A = A} {B = B} f a γ = Tm-path λ δ → refl

  lam : Tm (Γ ▸ A) B bˢ → Tm Γ (A ⇒ B) (S.lam bˢ)
  ∣ lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b ∣ γ .syn = S.lam bˢ S.[ Γ .map γ ]
  ∣ lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b ∣ γ .sem = λ x a → ∣ b ∣ ((Γ ! γ [ x ]) , a)
  ∣ lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b ∣ γ .![] = λ x a y → (λ i → ∣ b ∣ ((Γ .![]-∘ γ x y i) , (A ! a [ y ]))) ∙ b .![] (Γ ! γ [ x ] , a) y
  ∣ lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b ∣ γ .map = λ x a → b .map (Γ ! γ [ x ] , a) 
        ∙ (λ i → bˢ S.[ Γ .map-[] γ x i S., A .map a ])
        ∙ (λ i → bˢ S.[ sym (S.↑-⟨⟩ (map Γ γ S.∘ Wk-emb x) (A .map a)) i ])
        ∙ (λ i → bˢ S.[ S.↑-∘ (map Γ γ) (Wk-emb x) i S.∘ S.⟨ map A a ⟩ ])
        ∙ S.[]-∘ bˢ ((map Γ γ S.↑) S.∘ (Wk-emb x S.↑)) (S.⟨ map A a ⟩)
        ∙  (λ i → S.[]-∘ bˢ (map Γ γ S.↑) (Wk-emb x S.↑ ) i S.[ S.⟨ map A a ⟩ ]) 
        ∙  sym (S.⇒-β ((bˢ S.[ map Γ γ S.↑ ]) S.[ Wk-emb x S.↑ ]) (map A a))
        ∙  (λ i → S.app (S.lam-[] (bˢ S.[ map Γ γ S.↑ ]) (Wk-emb x) (~ i)) ((map A a))) 
        ∙ λ i → S.app (S.lam-[] bˢ ( map Γ γ) (~ i) S.[ Wk-emb x ]) (map A a) 
  lam {Γ = Γ} {bˢ = bˢ} b .![] γ x = Fun-path
    ((λ i → (S.lam bˢ S.[ Γ .map-[] γ x i ])) ∙ S.[]-∘ (S.lam bˢ) (Γ .map γ) (Wk-emb x))
    (λ x₁ a i → ∣ b ∣ ((Γ .![]-∘ γ x x₁ (~ i)) , a))
    
  lam b .map γ = refl

  lam-[] :
    (b : Tm (Γ ▸ A) B bˢ) (γ : Sub Δ Γ γˢ) →
    lam b [ γ ] ≡ᵗ[ S.lam-[] _ _ ] lam (b [ γ ↑ ])
  lam-[] {Γ = Γ} {bˢ = bˢ} {Δ = Δ} {γˢ = γˢ} b γ = Tm-path (λ δ → Fun-path 
    ((λ i → S.lam bˢ S.[ γ .map δ i ]) ∙ S.[]-∘ (S.lam bˢ) γˢ (map Δ δ) ∙ λ i → (S.lam-[] bˢ γˢ i S.[ map Δ δ ])) 
    (λ x a i → ∣ b ∣ ((γ .![] δ x (~ i)) , a)))

  ⇒-β :
    (b : Tm (Γ ▸ A) B bˢ) (a : Tm Γ A aˢ) →
    app (lam b) a ≡ᵗ[ S.⇒-β _ _ ] b [ ⟨ a ⟩ ]
  ⇒-β {Γ = Γ} b a = Tm-path λ γ i → ∣ b ∣ ((Γ .![]-id γ i) , (∣ a ∣ γ))

  ⇒-η : (f : Tm Γ (A ⇒ B) fˢ) → lam (app (f [ p ]) q) ≡ᵗ[ S.⇒-η _ ] f
  ⇒-η {Γ = Γ} {A = A} {B = B} {fˢ = fˢ} f = Tm-path (λ γ → Fun-path
    ( (λ i → S.⇒-η fˢ i S.[ Γ .map γ ]) ∙ sym (f .map γ) )
    ( λ x a → (λ i → f .![] γ x i .sem W.id' a) ∙ (λ i → ∣ f ∣ γ .sem (W.idr' x i) a)
    ))

  ⊥ₗ : Ty S.⊥ₗ 
  ∣ ⊥ₗ ∣ X = Co.Cov (λ _ → ⊥) X , {!   !}  -- isSet for Cov ⊥
  (⊥ₗ ! c [ x ]) = Co.wkCov (λ v _ → exfalso v) c x
  ⊥ₗ .![]-∘ c x y = Co.wkCov⊥-∘ c x y
  ⊥ₗ .![]-id c = Co.wkCov⊥-id c
  ⊥ₗ .map c = Co.runTm (Co.fmapCov (λ v → exfalso v) c)
  ⊥ₗ .map-[] c x = Co.runTm-fmap⊥-wkCov c x
  ⊥ₗ .quo c = Co.fmapCov (λ v → exfalso v) c
  ⊥ₗ .quo-[] c x = Co.fmap⊥-wkCov c x
  ⊥ₗ .emb-quo c = Co.embCov-runTm-fmap⊥ c
  ⊥ₗ .ref ne = Co.abort ne
  ⊥ₗ .ref-[] ne x = refl
  ⊥ₗ .map-ref ne = sym (S.⊥ₗ-η (Ne-emb ne))
  ⊥ₗ .abort-sem ne = Co.abort ne
  ⊥ₗ .abort-sem-[] ne x = refl
  ⊥ₗ .map-exfalso ne = refl
  ⊥ₗ .run c = Co.joinCov c
  ⊥ₗ .run-[] c x = Co.joinCov-wkCov⊥ c x
  ⊥ₗ .map-run c = Co.runTm-fmap-joinCov⊥ c
  ⊥ₗ .run-return a = refl
  ⊥ₗ .run-abort ne = refl
  ⊥ₗ .run-case ne c1 c2 = refl

  exfalsoₗ : Tm Γ ⊥ₗ tˢ → Tm Γ A (S.exfalsoₗ tˢ)
  ∣ exfalsoₗ {A = A} t ∣ γ = A .run (Co.fmapCov (λ v → exfalso v) (∣ t ∣ γ))
  
  exfalsoₗ {Γ = Γ} {A = A} t .![] γ x' = 
      (λ i → A .run (Co.fmapCov (λ v → exfalso v) (t .![] γ x' i)))
    ∙ (λ i → A .run (Co.fmapCov-exf-wkCov⊥ (Ty._[_] A) (λ v → exfalso v) (∣ t ∣ γ) x' i))
    ∙ A .run-[] (Co.fmapCov (λ v → exfalso v) (∣ t ∣ γ)) x'
    
  exfalsoₗ {Γ = Γ} {tˢ = tˢ} {A = A} t .map γ = 
      A .map-run (Co.fmapCov (λ v → exfalso v) (∣ t ∣ γ))
    ∙ cong Co.runTm (Co.fmapCov-∘ (A .map) (λ v → exfalso v) (∣ t ∣ γ))
    ∙ Co.runTm-fmapCov-exf (λ v → A .map (exfalso v)) (∣ t ∣ γ)
    ∙ (λ i → S.exfalsoₗ (t .map γ i))
    ∙ sym (S.exfalsoₗ-[] tˢ (Γ .map γ))
    
  exfalsoₗ-[] : (t : Tm Γ ⊥ₗ tˢ) (γ : Sub Δ Γ γˢ) → exfalsoₗ {A = A} t [ γ ] ≡ᵗ[ S.exfalsoₗ-[] _ _ ] exfalsoₗ (t [ γ ])
  exfalsoₗ-[] t γ = Tm-path λ δ → refl

  ⊥ₗ-η : ∀ {Γˢ} {Γ : Con Γˢ} {tˢ : S.Tm Γˢ S.⊥ₗ} (t : Tm Γ ⊥ₗ tˢ) 
        → t ≡ᵗ[ S.⊥ₗ-η tˢ ] exfalsoₗ {A = ⊥ₗ} t
  ⊥ₗ-η t = Tm-path (λ γ → Co.⊥-η-Cov (∣ t ∣ γ))

  -- applying run of exfalso-cover at ⇒ type gives run at B
  π-⇒0-helper : ∀ {Aˢ Bˢ X} {A : Ty Aˢ} {B : Ty Bˢ}
    (a : fst (∣ A ∣ X)) (c : Co.Cov (λ _ → ⊥) X) →
    (A ⇒ B) .run (Co.fmapCov (λ v → exfalso v) c) .sem W.id' a 
    ≡ B .run (Co.fmapCov (λ v → exfalso v) c)
  π-⇒0-helper a (Co.return v) = exfalso v
  π-⇒0-helper {A = A} {B = B} a (Co.abort ne) = 
      B .run-abort (ne N.[ W.id' ]ᴺᵉ) 
    ∙ (λ i → B .abort-sem (N.[]ᴺᵉ-id ne i)) 
    ∙ sym (B .run-abort ne)
  π-⇒0-helper {A = A} {B = B} a (Co.case {A = A₁} {B = B₁} ne c1 c2) = 
    let rec₁ = π-⇒0-helper {A = A} {B = B} (A ! a [ W._∘p {A = A₁} W.id' ]) c1
        rec₂ = π-⇒0-helper {A = A} {B = B} (A ! a [ W._∘p {A = B₁} W.id' ]) c2
    in cong (λ g → g .sem W.id' a) ((A ⇒ B) .run-case ne (Co.fmapCov (λ v → exfalso v) c1) (Co.fmapCov (λ v → exfalso v) c2))
     ∙ (λ i → B .run (Co.case (ne N.[ W.id' ]ᴺᵉ)
               (Co.return (((A ⇒ B) .run (Co.fmapCov (λ v → exfalso v) c1)) .sem (W.idr' (W._↑' {A = A₁} W.id') i) (A ! a [ W.idr' (W._∘p {A = A₁} W.id') i ])))
               (Co.return (((A ⇒ B) .run (Co.fmapCov (λ v → exfalso v) c2)) .sem (W.idr' (W._↑' {A = B₁} W.id') i) (A ! a [ W.idr' (W._∘p {A = B₁} W.id') i ])))))
     ∙ (λ i → B .run (Co.case (ne N.[ W.id' ]ᴺᵉ) (Co.return (rec₁ i)) (Co.return (rec₂ i))))
     ∙ (λ i → B .run (Co.case (N.[]ᴺᵉ-id ne i) (Co.return (B .run (Co.fmapCov (λ v → exfalso v) c1))) (Co.return (B .run (Co.fmapCov (λ v → exfalso v) c2)))))
     ∙ sym (B .run-case ne (Co.fmapCov (λ v → exfalso v) c1) (Co.fmapCov (λ v → exfalso v) c2))

  π-⇒0 : ∀ {Γˢ Aˢ Bˢ} {Γ : Con Γˢ} {A : Ty Aˢ} {B : Ty Bˢ} {tˢ : S.Tm Γˢ S.⊥ₗ} {aˢ : S.Tm Γˢ Aˢ} 
         (t : Tm Γ ⊥ₗ tˢ) (a : Tm Γ A aˢ) 
       → app (exfalsoₗ {A = A ⇒ B} t) a ≡ᵗ[ S.π-⇒0 tˢ aˢ ] exfalsoₗ {A = B} t
  π-⇒0 {A = A} {B = B} t a = Tm-path (λ γ → π-⇒0-helper (∣ a ∣ γ) (∣ t ∣ γ))

  -- [[A + B]] = C([[A]] + [[B]]) 
  wk+ : ∀ {Aˢ Bˢ} (A : Ty Aˢ) (B : Ty Bˢ) {X Y} → fst (∣ A ∣ X) ⊎ fst (∣ B ∣ X) → W.Wk Y X → fst (∣ A ∣ Y) ⊎ fst (∣ B ∣ Y)
  wk+ A B (inl a) w = inl (A ! a [ w ])
  wk+ A B (inr b) w = inr (B ! b [ w ])

  map+ : ∀ {Aˢ Bˢ} (A : Ty Aˢ) (B : Ty Bˢ) {Δ} → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ) → S.Tm Δ (Aˢ S.+ Bˢ)
  map+ A B (inl a) = S.inl (A .map a)
  map+ A B (inr b) = S.inr (B .map b)

  eval-case : ∀ {Γˢ Aˢ Bˢ Cˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {Γ : Con Γˢ} {bˢ cˢ}
    (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ)
    (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) → Co.Cov (λ Δ → fst (∣ C ∣ Δ)) X
  eval-case l r γ (Co.return (inl a)) = Co.return (∣ l ∣ (γ , a))
  eval-case l r γ (Co.return (inr b)) = Co.return (∣ r ∣ (γ , b))
  eval-case l r γ (Co.abort ne) = Co.abort ne
  eval-case {Γ = Γ} l r γ (Co.case ne c1 c2) = Co.case ne 
    (eval-case l r (Γ ! γ [ W.id' W.∘p ]) c1) 
    (eval-case l r (Γ ! γ [ W.id' W.∘p ]) c2)

  eval-case-![] : ∀ {Γˢ Aˢ Bˢ Cˢ X Y} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {Γ : Con Γˢ} {bˢ cˢ}
    (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ)
    (γ : fst (∣ Γ ∣ X)) (x : W.Wk Y X) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) →
    eval-case l r (Γ ! γ [ x ]) (Co.wkCov (wk+ A B) c x) 
    ≡ Co.wkCov (Ty._[_] C) (eval-case l r γ c) x
  eval-case-![] l r γ x (Co.return (inl a)) = λ i → Co.return (l .![] (γ , a) x i)
  eval-case-![] l r γ x (Co.return (inr b)) = λ i → Co.return (r .![] (γ , b) x i)
  eval-case-![] l r γ x (Co.abort ne) = refl
  eval-case-![] {A = A} {B = B} {C = C} {Γ = Γ} l r γ x (Co.case {A = A₁} {B = B₁} ne c1 c2) = 
    let γ-wk₁ = sym (Γ .![]-∘ γ x (W.id' W.∘p)) 
                ∙ (λ i → Γ ! γ [ Co.wk-comm {A = A₁} x i ]) 
                ∙ Γ .![]-∘ γ (W.id' W.∘p) (x W.↑')
        γ-wk₂ = sym (Γ .![]-∘ γ x (W.id' W.∘p)) 
                ∙ (λ i → Γ ! γ [ Co.wk-comm {A = B₁} x i ]) 
                ∙ Γ .![]-∘ γ (W.id' W.∘p) (x W.↑')
        rec₁ = eval-case-![] l r (Γ ! γ [ W.id' W.∘p ]) (x W.↑') c1
        rec₂ = eval-case-![] l r (Γ ! γ [ W.id' W.∘p ]) (x W.↑') c2
    in (λ i → Co.case (ne N.[ x ]ᴺᵉ)
         (eval-case l r (γ-wk₁ i) (Co.wkCov (wk+ A B) c1 (x W.↑')))
         (eval-case l r (γ-wk₂ i) (Co.wkCov (wk+ A B) c2 (x W.↑'))))
       ∙ (λ i → Co.case (ne N.[ x ]ᴺᵉ) (rec₁ i) (rec₂ i))

  eval-case-map : ∀ {Γˢ Aˢ Bˢ Cˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {Γ : Con Γˢ} {bˢ cˢ}
    (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ)
    (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) →
    Co.runTm (Co.fmapCov (C .map) (eval-case l r γ c)) 
    ≡ S.caseₗ (Co.runTm (Co.fmapCov (map+ A B) c)) (bˢ S.[ Γ .map γ S.↑ ]) (cˢ S.[ Γ .map γ S.↑ ])
  eval-case-map {A = A} {C = C} {Γ = Γ} {bˢ = bˢ} {cˢ = cˢ} l r γ (Co.return (inl a)) = 
      (λ i → C .map (∣ l ∣ (γ , a)))
    ∙ l .map (γ , a)
    ∙ (λ i → bˢ S.[ Γ .map γ S., A .map a ])
    ∙ (λ i → bˢ S.[ sym (S.↑-⟨⟩ (Γ .map γ) (A .map a)) i ])
    ∙ S.[]-∘ bˢ (Γ .map γ S.↑) (S.⟨ A .map a ⟩)
    ∙ sym (S.+-β₁ (A .map a) (bˢ S.[ Γ .map γ S.↑ ]) (cˢ S.[ Γ .map γ S.↑ ]))
  eval-case-map {B = B} {C = C} {Γ = Γ} {bˢ = bˢ} {cˢ = cˢ} l r γ (Co.return (inr b)) = 
      (λ i → C .map (∣ r ∣ (γ , b)))
    ∙ r .map (γ , b)
    ∙ (λ i → cˢ S.[ Γ .map γ S., B .map b ])
    ∙ (λ i → cˢ S.[ sym (S.↑-⟨⟩ (Γ .map γ) (B .map b)) i ])
    ∙ S.[]-∘ cˢ (Γ .map γ S.↑) (S.⟨ B .map b ⟩)
    ∙ sym (S.+-β₂ (B .map b) (bˢ S.[ Γ .map γ S.↑ ]) (cˢ S.[ Γ .map γ S.↑ ]))
  eval-case-map {Γ = Γ} {bˢ = bˢ} {cˢ = cˢ} l r γ (Co.abort ne) = 
    sym (S.π-⇒+ (Ne-emb ne) (bˢ S.[ Γ .map γ S.↑ ]) (cˢ S.[ Γ .map γ S.↑ ]))
  eval-case-map {A = A} {B = B} {C = C} {Γ = Γ} {bˢ = bˢ} {cˢ = cˢ} l r γ (Co.case {A = A₁} {B = B₁} ne c1 c2) = 
    let rec₁ = eval-case-map l r (Γ ! γ [ W.id' W.∘p ]) c1
        rec₂ = eval-case-map l r (Γ ! γ [ W.id' W.∘p ]) c2
        b' = bˢ S.[ Γ .map γ S.↑ ]
        c' = cˢ S.[ Γ .map γ S.↑ ]
        
        b-wk₁ = (λ i → bˢ S.[ Γ .map-[] γ (W.id' W.∘p) i S.↑ ])
                ∙ (λ i → bˢ S.[ (Γ .map γ S.∘ Co.wk-p-eq {A = A₁} i) S.↑ ])
                ∙ (λ i → bˢ S.[ S.↑-∘ (Γ .map γ) (S.p {A = A₁}) i ])
                ∙ S.[]-∘ bˢ (Γ .map γ S.↑) (S.p {A = A₁} S.↑)
                
        c-wk₁ = (λ i → cˢ S.[ Γ .map-[] γ (W.id' W.∘p) i S.↑ ])
                ∙ (λ i → cˢ S.[ (Γ .map γ S.∘ Co.wk-p-eq {A = A₁} i) S.↑ ])
                ∙ (λ i → cˢ S.[ S.↑-∘ (Γ .map γ) (S.p {A = A₁}) i ])
                ∙ S.[]-∘ cˢ (Γ .map γ S.↑) (S.p {A = A₁} S.↑)
                
        b-wk₂ = (λ i → bˢ S.[ Γ .map-[] γ (W.id' W.∘p) i S.↑ ])
                ∙ (λ i → bˢ S.[ (Γ .map γ S.∘ Co.wk-p-eq {A = B₁} i) S.↑ ])
                ∙ (λ i → bˢ S.[ S.↑-∘ (Γ .map γ) (S.p {A = B₁}) i ])
                ∙ S.[]-∘ bˢ (Γ .map γ S.↑) (S.p {A = B₁} S.↑)
                
        c-wk₂ = (λ i → cˢ S.[ Γ .map-[] γ (W.id' W.∘p) i S.↑ ])
                ∙ (λ i → cˢ S.[ (Γ .map γ S.∘ Co.wk-p-eq {A = B₁} i) S.↑ ])
                ∙ (λ i → cˢ S.[ S.↑-∘ (Γ .map γ) (S.p {A = B₁}) i ])
                ∙ S.[]-∘ cˢ (Γ .map γ S.↑) (S.p {A = B₁} S.↑)
                
    in (λ i → S.caseₗ (Ne-emb ne) (rec₁ i) (rec₂ i))
       ∙ (λ i → S.caseₗ (Ne-emb ne) 
           (S.caseₗ (Co.runTm (Co.fmapCov (map+ A B) c1)) (b-wk₁ i) (c-wk₁ i))
           (S.caseₗ (Co.runTm (Co.fmapCov (map+ A B) c2)) (b-wk₂ i) (c-wk₂ i)))
       ∙ sym (S.π-++ (Ne-emb ne) (Co.runTm (Co.fmapCov (map+ A B) c1)) (Co.runTm (Co.fmapCov (map+ A B) c2)) b' c')

  quo+ : ∀ {Aˢ Bˢ} (A : Ty Aˢ) (B : Ty Bˢ) {Δ} → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ) → N.Nf Δ (Aˢ S.+ Bˢ)
  quo+ A B (inl a) = N.inl (Co.runNf (A .quo a))
  quo+ A B (inr b) = N.inr (Co.runNf (B .quo b))

  infixl 7 _+ₛ_
  _+ₛ_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.+ Bˢ)
  ∣ A +ₛ B ∣ X = Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X , {!   !}
  (A +ₛ B) ! c [ x ] = Co.wkCov (wk+ A B) c x
  (A +ₛ B) .![]-∘ c x y = Co.wkCov-∘ (wk+ A B)
    (λ { (inl a) x' y' → cong inl (A .![]-∘ a x' y') ; (inr b) x' y' → cong inr (B .![]-∘ b x' y') })
    c x y
  (A +ₛ B) .![]-id c = Co.wkCov-id (wk+ A B)
    (λ { (inl a) → cong inl (A .![]-id a) ; (inr b) → cong inr (B .![]-id b) })
    c
  (A +ₛ B) .map c = Co.runTm (Co.fmapCov (map+ A B) c)
  (A +ₛ B) .map-[] c x = Co.runTm-fmapCov-wkCov (wk+ A B) (map+ A B)
    (λ { (inl a) w → (λ i → S.inl (A .map-[] a w i)) ∙ sym (S.inl-[] (A .map a) (W.Wk-emb w))
       ; (inr b) w → (λ i → S.inr (B .map-[] b w i)) ∙ sym (S.inr-[] (B .map b) (W.Wk-emb w)) })
    c x
  (A +ₛ B) .quo c = Co.fmapCov (quo+ A B) c
  (A +ₛ B) .quo-[] c x = Co.fmapCov-wkCov (wk+ A B) (λ nf w → nf N.[ w ]ᴺᶠ) (quo+ A B)
    (λ { (inl a) w → (λ i → N.inl (Co.runNf (A .quo-[] a w i))) ∙ (λ i → N.inl (Co.runNf-[] (A .quo a) w i))
       ; (inr b) w → (λ i → N.inr (Co.runNf (B .quo-[] b w i))) ∙ (λ i → N.inr (Co.runNf-[] (B .quo b) w i)) })
    c x
  (A +ₛ B) .emb-quo c = Co.embCov-fmapCov (quo+ A B) c ∙ emb-quo-h c
    where
      emb-quo-h : ∀ {X} (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X)
        → Co.runTm (Co.fmapCov (λ p → Nf-emb (quo+ A B p)) c) ≡ Co.runTm (Co.fmapCov (map+ A B) c)
      emb-quo-h (Co.return (inl a)) = (λ i → S.inl (Co.emb-runNf (A .quo a) i)) ∙ (λ i → S.inl (A .emb-quo a i))
      emb-quo-h (Co.return (inr b)) = (λ i → S.inr (Co.emb-runNf (B .quo b) i)) ∙ (λ i → S.inr (B .emb-quo b i))
      emb-quo-h (Co.abort ne) = refl
      emb-quo-h (Co.case ne c1 c2) = λ i → S.caseₗ (Ne-emb ne) (emb-quo-h c1 i) (emb-quo-h c2 i)
  (A +ₛ B) .ref ne = Co.case ne (Co.return (inl (A .ref (N.var W.q)))) (Co.return (inr (B .ref (N.var W.q))))
  (A +ₛ B) .ref-[] ne x = λ i → Co.case (ne N.[ x ]ᴺᵉ) (Co.return (inl (A .ref-[] (N.var W.q) (x W.↑') i))) (Co.return (inr (B .ref-[] (N.var W.q) (x W.↑') i)))
  (A +ₛ B) .map-ref ne = (λ i → S.caseₗ (Ne-emb ne) (S.inl (A .map-ref (N.var W.q) i)) (S.inr (B .map-ref (N.var W.q) i))) ∙ S.+-η (Ne-emb ne)
  (A +ₛ B) .abort-sem ne = Co.abort ne
  (A +ₛ B) .abort-sem-[] ne x = refl
  (A +ₛ B) .map-exfalso ne = refl
  (A +ₛ B) .run c = Co.joinCov c
  (A +ₛ B) .run-[] c x = Co.joinCov-wkCov (wk+ A B) c x
  (A +ₛ B) .map-run c = Co.runTm-fmapCov-joinCov (map+ A B) c
  (A +ₛ B) .run-return a = refl
  (A +ₛ B) .run-abort ne = refl
  (A +ₛ B) .run-case ne c1 c2 = refl

  inlₛ : Tm Γ A aˢ → Tm Γ (A +ₛ B) (S.inl aˢ)
  ∣ inlₛ a ∣ γ = Co.return (inl (∣ a ∣ γ))
  inlₛ a .![] γ x = λ i → Co.return (inl (a .![] γ x i))
  inlₛ {A = A} {aˢ = aˢ} a .map γ = 
      (λ i → S.inl (a .map γ i))
    ∙ sym (S.inl-[] aˢ _)

  inrₛ : Tm Γ B bˢ → Tm Γ (A +ₛ B) (S.inr bˢ)
  ∣ inrₛ b ∣ γ = Co.return (inr (∣ b ∣ γ))
  inrₛ b .![] γ x = λ i → Co.return (inr (b .![] γ x i))
  inrₛ {B = B} {bˢ = bˢ} b .map γ = 
      (λ i → S.inr (b .map γ i))
    ∙ sym (S.inr-[] bˢ _)

  caseₗₛ : Tm Γ (A +ₛ B) aˢ → Tm (Γ ▸ A) C bˢ → Tm (Γ ▸ B) C cˢ → Tm Γ C (S.caseₗ aˢ bˢ cˢ)
  ∣ caseₗₛ {C = C} s l r ∣ γ = C .run (eval-case l r γ (∣ s ∣ γ))
  
  caseₗₛ {Γ = Γ} {C = C} s l r .![] γ x = 
      (λ i → C .run (eval-case l r (Γ ! γ [ x ]) (s .![] γ x i)))
    ∙ (λ i → C .run (eval-case-![] l r γ x (∣ s ∣ γ) i))
    ∙ C .run-[] (eval-case l r γ (∣ s ∣ γ)) x
    
  caseₗₛ {Γ = Γ} {aˢ = aˢ}{C = C} {bˢ = bˢ} {cˢ = cˢ}  s l r .map γ = 
      C .map-run (eval-case l r γ (∣ s ∣ γ))
    ∙ eval-case-map l r γ (∣ s ∣ γ)
    ∙ (λ i → S.caseₗ (s .map γ i) (bˢ S.[ map Γ γ S.↑ ]) (cˢ S.[ map Γ γ S.↑ ]))
    ∙ λ i → S.caseₗ-[] aˢ bˢ cˢ (Γ .map γ) (~ i) 

  inl-[]ₛ : (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) → inlₛ {B = B} a [ γ ] ≡ᵗ[ S.inl-[] aˢ γˢ ] inlₛ (a [ γ ])
  inl-[]ₛ a γ = Tm-path λ δ → refl

  inr-[]ₛ : (b : Tm Γ B bˢ) (γ : Sub Δ Γ γˢ) → inrₛ {A = A} b [ γ ] ≡ᵗ[ S.inr-[] bˢ γˢ ] inrₛ (b [ γ ])
  inr-[]ₛ b γ = Tm-path λ δ → refl

  eval-case-[]ₛ : ∀ {Γˢ Δˢ Aˢ Bˢ Cˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {Γ : Con Γˢ} {Δ : Con Δˢ} {bˢ cˢ γˢ}
    (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ) (γ : Sub Δ Γ γˢ)
    (δ : fst (∣ Δ ∣ X)) (c : Co.Cov (λ Θ → fst (∣ A ∣ Θ) ⊎ fst (∣ B ∣ Θ)) X) →
    eval-case (l [ γ ↑ ]) (r [ γ ↑ ]) δ c ≡ eval-case l r (∣ γ ∣ δ) c
  eval-case-[]ₛ l r γ δ (Co.return (inl a)) = refl
  eval-case-[]ₛ l r γ δ (Co.return (inr b)) = refl
  eval-case-[]ₛ l r γ δ (Co.abort ne) = refl
  eval-case-[]ₛ {A = A} {B = B} {C = C} {Γ = Γ} {Δ = Δ} l r γ δ (Co.case {A = A₁} {B = B₁} ne c1 c2) =
    (λ i → Co.case ne (eval-case-[]ₛ l r γ (Δ ! δ [ W.id' W.∘p ]) c1 i) (eval-case-[]ₛ l r γ (Δ ! δ [ W.id' W.∘p ]) c2 i))
    ∙ (λ i → Co.case ne (eval-case l r (γ .![] δ (W.id' W.∘p) i) c1) (eval-case l r (γ .![] δ (W.id' W.∘p) i) c2))

  caseₗ-[]ₛ : (s : Tm Γ (A +ₛ B) aˢ) (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ) (γ : Sub Δ Γ γˢ)
           → caseₗₛ s l r [ γ ] ≡ᵗ[ S.caseₗ-[] aˢ bˢ cˢ γˢ ] caseₗₛ (s [ γ ]) (l [ γ ↑ ]) (r [ γ ↑ ])
  caseₗ-[]ₛ {C = C} s l r γ = Tm-path λ δ i → 
    C .run (eval-case-[]ₛ l r γ δ (∣ s ∣ (∣ γ ∣ δ)) (~ i))

  +-β₁ₛ : (a : Tm Γ A aˢ) (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ) → caseₗₛ (inlₛ {B = B} a) l r ≡ᵗ[ S.+-β₁ aˢ bˢ cˢ ] l [ ⟨ a ⟩ ]
  +-β₁ₛ {C = C} a l r = Tm-path λ γ i → C .run-return (∣ l ∣ (γ , ∣ a ∣ γ)) i

  +-β₂ₛ : (b : Tm Γ B bˢ) (l : Tm (Γ ▸ A) C aˢ) (r : Tm (Γ ▸ B) C cˢ) → caseₗₛ (inrₛ {A = A} b) l r ≡ᵗ[ S.+-β₂ bˢ aˢ cˢ ] r [ ⟨ b ⟩ ]
  +-β₂ₛ {C = C} b l r = Tm-path λ γ i → C .run-return (∣ r ∣ (γ , ∣ b ∣ γ)) i

  +-η-helper : ∀ {Γˢ Aˢ Bˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {Γ : Con Γˢ} 
               (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) → 
               Co.joinCov (eval-case {A = A} {B = B} {C = A +ₛ B} {Γ = Γ} 
                 (inlₛ {B = B} (q {Γ = Γ} {A = A})) 
                 (inrₛ {A = A} (q {Γ = Γ} {A = B})) 
                 γ c) ≡ c
  +-η-helper γ (Co.return (inl a)) = refl
  +-η-helper γ (Co.return (inr b)) = refl
  +-η-helper γ (Co.abort ne) = refl
  +-η-helper {A = A} {B = B} {Γ = Γ} γ (Co.case ne c1 c2) = 
    λ i → Co.case ne (+-η-helper {A = A} {B = B} {Γ = Γ} (Γ ! γ [ W.id' W.∘p ]) c1 i) 
                     (+-η-helper {A = A} {B = B} {Γ = Γ} (Γ ! γ [ W.id' W.∘p ]) c2 i)

  +-ηₛ : (s : Tm Γ (A +ₛ B) aˢ) → caseₗₛ s (inlₛ {B = B} (q {Γ = Γ} {A = A})) (inrₛ {A = A} (q {Γ = Γ} {A = B})) ≡ᵗ[ S.+-η aˢ ] s
  +-ηₛ {Γ = Γ}{A = A} {B = B}  s = Tm-path λ γ i → +-η-helper {A = A} {B = B} {Γ = Γ} γ (∣ s ∣ γ) i

  eval-case-app : ∀ {Γˢ Aˢ Bˢ Cˢ Dˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {D : Ty Dˢ} {Γ : Con Γˢ} {bˢ cˢ fˢ}
    (l : Tm (Γ ▸ A) (C ⇒ D) bˢ) (r : Tm (Γ ▸ B) (C ⇒ D) cˢ)
    (u : Tm Γ C fˢ)
    (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) →
    (C ⇒ D) .run (eval-case l r γ c) .sem W.id' (∣ u ∣ γ)
    ≡ D .run (eval-case (app l (u [ p ])) (app r (u [ p ])) γ c)
  eval-case-app {C = C} {D = D} l r u γ (Co.return (inl a)) = 
    cong (λ g → g .sem W.id' (∣ u ∣ γ)) ((C ⇒ D) .run-return (∣ l ∣ (γ , a)))
    ∙ sym (D .run-return (∣ l ∣ (γ , a) .sem W.id' (∣ u ∣ γ)))
  eval-case-app {C = C} {D = D} l r u γ (Co.return (inr b)) = 
    cong (λ g → g .sem W.id' (∣ u ∣ γ)) ((C ⇒ D) .run-return (∣ r ∣ (γ , b)))
    ∙ sym (D .run-return (∣ r ∣ (γ , b) .sem W.id' (∣ u ∣ γ)))
  eval-case-app {C = C} {D = D} l r u γ (Co.abort ne) = 
    cong (λ g → g .sem W.id' (∣ u ∣ γ)) ((C ⇒ D) .run-abort ne)
    ∙ (λ i → D .abort-sem (N.[]ᴺᵉ-id ne i))
    ∙ sym (D .run-abort ne)
  eval-case-app {A = A₁} {B = B₁} {C = C} {D = D} {Γ = Γ} l r u γ (Co.case {A = Aᶜ} {B = Bᶜ} ne c1 c2) = 
    let γ₁ = Γ ! γ [ W._∘p {A = Aᶜ} W.id' ]
        γ₂ = Γ ! γ [ W._∘p {A = Bᶜ} W.id' ]
        rec₁ = eval-case-app {A = A₁} {B = B₁} l r u γ₁ c1
        rec₂ = eval-case-app {A = A₁} {B = B₁} l r u γ₂ c2
        lhs-d1 = eval-case l r γ₁ c1
        lhs-d2 = eval-case l r γ₂ c2
        rhs-d1 = eval-case (app l (u [ p ])) (app r (u [ p ])) γ₁ c1
        rhs-d2 = eval-case (app l (u [ p ])) (app r (u [ p ])) γ₂ c2
    in cong (λ f → f .sem W.id' (∣ u ∣ γ)) ((C ⇒ D) .run-case ne lhs-d1 lhs-d2)
     ∙ (λ i → D .run (Co.case (ne N.[ W.id' ]ᴺᵉ)
               (Co.return (((C ⇒ D) .run lhs-d1) .sem (W.idr' (W._↑' {A = Aᶜ} W.id') i) (C ! (∣ u ∣ γ) [ W.idr' (W._∘p {A = Aᶜ} W.id') i ])))
               (Co.return (((C ⇒ D) .run lhs-d2) .sem (W.idr' (W._↑' {A = Bᶜ} W.id') i) (C ! (∣ u ∣ γ) [ W.idr' (W._∘p {A = Bᶜ} W.id') i ])))))
     ∙ (λ i → D .run (Co.case (ne N.[ W.id' ]ᴺᵉ)
               (Co.return (((C ⇒ D) .run lhs-d1) .sem W.id' (u .![] γ (W._∘p {A = Aᶜ} W.id') (~ i))))
               (Co.return (((C ⇒ D) .run lhs-d2) .sem W.id' (u .![] γ (W._∘p {A = Bᶜ} W.id') (~ i))))))
     ∙ (λ i → D .run (Co.case (ne N.[ W.id' ]ᴺᵉ) (Co.return (rec₁ i)) (Co.return (rec₂ i))))
     ∙ (λ i → D .run (Co.case (N.[]ᴺᵉ-id ne i) (Co.return (D .run rhs-d1)) (Co.return (D .run rhs-d2))))
     ∙ sym (D .run-case ne rhs-d1 rhs-d2)

  π-+⇒ₛ : ∀ {D : Ty Dˢ} (s : Tm Γ (A +ₛ B) aˢ) (l : Tm (Γ ▸ A) (C ⇒ D) bˢ) (r : Tm (Γ ▸ B) (C ⇒ D) cˢ) (u : Tm Γ C fˢ)
       → app (caseₗₛ s l r) u ≡ᵗ[ S.π-+⇒ aˢ bˢ cˢ fˢ ] caseₗₛ s (app l (u [ p ])) (app r (u [ p ]))
  π-+⇒ₛ {D = D} s l r u = Tm-path (λ γ → eval-case-app l r u γ (∣ s ∣ γ))

  eval-case-exfalso : ∀ {Γˢ Aˢ Bˢ Cˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {Γ : Con Γˢ} {bˢ cˢ}
    (l : Tm (Γ ▸ A) ⊥ₗ bˢ) (r : Tm (Γ ▸ B) ⊥ₗ cˢ)
    (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) →
    C .run (Co.fmapCov (λ v → exfalso v) (Co.joinCov (eval-case l r γ c)))
    ≡ C .run (eval-case (exfalsoₗ {A = C} l) (exfalsoₗ {A = C} r) γ c)
  eval-case-exfalso {C = C} l r γ (Co.return (inl a)) = 
    sym (C .run-return (C .run (Co.fmapCov (λ v → exfalso v) (∣ l ∣ (γ , a)))))
  eval-case-exfalso {C = C} l r γ (Co.return (inr b)) = 
    sym (C .run-return (C .run (Co.fmapCov (λ v → exfalso v) (∣ r ∣ (γ , b)))))
  eval-case-exfalso l r γ (Co.abort ne) = refl
  eval-case-exfalso {C = C} {Γ = Γ} l r γ (Co.case {A = Aᶜ} {B = Bᶜ} ne c1 c2) =
    let γ₁ = Γ ! γ [ W._∘p {A = Aᶜ} W.id' ]
        γ₂ = Γ ! γ [ W._∘p {A = Bᶜ} W.id' ]
    in C .run-case ne _ _
     ∙ (λ i → C .run (Co.case ne (Co.return (eval-case-exfalso {C = C} l r γ₁ c1 i))
                                       (Co.return (eval-case-exfalso {C = C} l r γ₂ c2 i))))
     ∙ sym (C .run-case ne _ _)

  π-+0ₛ : (s : Tm Γ (A +ₛ B) aˢ) (l : Tm (Γ ▸ A) ⊥ₗ bˢ) (r : Tm (Γ ▸ B) ⊥ₗ cˢ)
       → exfalsoₗ {A = C} (caseₗₛ s l r) ≡ᵗ[ S.π-+0 aˢ bˢ cˢ ] caseₗₛ s (exfalsoₗ l) (exfalsoₗ r)
  π-+0ₛ {A = A} {B = B} {C = C} s l r = Tm-path λ γ →
    eval-case-exfalso {C = C} l r γ (∣ s ∣ γ)

  eval-case-joinCov : ∀ {Γˢ Aˢ Bˢ Cˢ Dˢ Eˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {D : Ty Dˢ} {E : Ty Eˢ} {Γ : Con Γˢ} {b₁ˢ c₁ˢ b₂ˢ c₂ˢ}
    (l₁ : Tm (Γ ▸ A) (C +ₛ D) b₁ˢ) (r₁ : Tm (Γ ▸ B) (C +ₛ D) c₁ˢ)
    (l₂ : Tm (Γ ▸ C) E b₂ˢ) (r₂ : Tm (Γ ▸ D) E c₂ˢ)
    (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ Δ → fst (∣ A ∣ Δ) ⊎ fst (∣ B ∣ Δ)) X) →
    E .run (eval-case l₂ r₂ γ (Co.joinCov (eval-case l₁ r₁ γ c)))
    ≡ E .run (eval-case (caseₗₛ l₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) (caseₗₛ r₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) γ c)
  eval-case-joinCov {A = A₁} {B = B₁} {C = C} {D = D} {E = E} {Γ = Γ} l₁ r₁ l₂ r₂ γ (Co.return (inl a)) = 
    sym (E .run-return (E .run (eval-case l₂ r₂ γ (∣ l₁ ∣ (γ , a)))))
    ∙ (λ i → E .run (Co.return (E .run (eval-case-[]ₛ l₂ r₂ (p {Γ = Γ} {A = A₁}) (γ , a) (∣ l₁ ∣ (γ , a)) (~ i)))))
  eval-case-joinCov {A = A₁} {B = B₁} {C = C} {D = D} {E = E} {Γ = Γ} l₁ r₁ l₂ r₂ γ (Co.return (inr b)) = 
    sym (E .run-return (E .run (eval-case l₂ r₂ γ (∣ r₁ ∣ (γ , b)))))
    ∙ (λ i → E .run (Co.return (E .run (eval-case-[]ₛ l₂ r₂ (p {Γ = Γ} {A = B₁}) (γ , b) (∣ r₁ ∣ (γ , b)) (~ i)))))
  eval-case-joinCov l₁ r₁ l₂ r₂ γ (Co.abort ne) = refl
  eval-case-joinCov {A = A₁} {B = B₁} {E = E} {Γ = Γ} l₁ r₁ l₂ r₂ γ (Co.case {A = Aᶜ} {B = Bᶜ} ne c1 c2) = 
    let γ₁ = Γ ! γ [ W._∘p {A = Aᶜ} W.id' ]
        γ₂ = Γ ! γ [ W._∘p {A = Bᶜ} W.id' ]
        rec₁ = eval-case-joinCov {A = A₁} {B = B₁} l₁ r₁ l₂ r₂ γ₁ c1
        rec₂ = eval-case-joinCov {A = A₁} {B = B₁} l₁ r₁ l₂ r₂ γ₂ c2
        lhs-branch1 = eval-case l₂ r₂ γ₁ (Co.joinCov (eval-case l₁ r₁ γ₁ c1))
        lhs-branch2 = eval-case l₂ r₂ γ₂ (Co.joinCov (eval-case l₁ r₁ γ₂ c2))
        rhs-branch1 = eval-case (caseₗₛ l₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) (caseₗₛ r₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) γ₁ c1
        rhs-branch2 = eval-case (caseₗₛ l₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) (caseₗₛ r₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) γ₂ c2
    in E .run-case ne lhs-branch1 lhs-branch2
     ∙ (λ i → E .run (Co.case ne (Co.return (rec₁ i)) (Co.return (rec₂ i))))
     ∙ sym (E .run-case ne rhs-branch1 rhs-branch2)

  π-++ₛ : ∀ {D : Ty Dˢ} {E : Ty Eˢ} (s : Tm Γ (A +ₛ B) aˢ) (l₁ : Tm (Γ ▸ A) (C +ₛ D) bˢ) (r₁ : Tm (Γ ▸ B) (C +ₛ D) cˢ)
         (l₂ : Tm (Γ ▸ C) E fˢ) (r₂ : Tm (Γ ▸ D) E tˢ)
       → caseₗₛ (caseₗₛ s l₁ r₁) l₂ r₂ ≡ᵗ[ S.π-++ aˢ bˢ cˢ fˢ tˢ ] caseₗₛ s (caseₗₛ l₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ])) (caseₗₛ r₁ (l₂ [ p ↑ ]) (r₂ [ p ↑ ]))
  π-++ₛ {E = E} s l₁ r₁ l₂ r₂ = Tm-path λ γ → eval-case-joinCov l₁ r₁ l₂ r₂ γ (∣ s ∣ γ)

  eval-case-exf : ∀ {Γˢ Aˢ Bˢ Cˢ X} {A : Ty Aˢ} {B : Ty Bˢ} {C : Ty Cˢ} {Γ : Con Γˢ} {bˢ cˢ}
    (l : Tm (Γ ▸ A) C bˢ) (r : Tm (Γ ▸ B) C cˢ)
    (γ : fst (∣ Γ ∣ X)) (c : Co.Cov (λ _ → ⊥) X) →
    eval-case l r γ (Co.joinCov (Co.fmapCov (λ v → exfalso v) c))
    ≡ Co.fmapCov (λ v → exfalso v) c
  eval-case-exf l r γ (Co.return v) = exfalso v
  eval-case-exf l r γ (Co.abort ne) = refl
  eval-case-exf {Γ = Γ} l r γ (Co.case ne c1 c2) =
    λ i → Co.case ne (eval-case-exf l r (Γ ! γ [ W.id' W.∘p ]) c1 i)
                      (eval-case-exf l r (Γ ! γ [ W.id' W.∘p ]) c2 i)

  π-⇒+ₛ : (t : Tm Γ ⊥ₗ tˢ) (l : Tm (Γ ▸ A) C aˢ) (r : Tm (Γ ▸ B) C bˢ)
       → caseₗₛ (exfalsoₗ {A = A +ₛ B} t) l r ≡ᵗ[ S.π-⇒+ tˢ aˢ bˢ ] exfalsoₗ {A = C} t
  π-⇒+ₛ {A = A} {C = C} {B = B} t l r = Tm-path λ γ →
    cong (C .run) (eval-case-exf l r γ (∣ t ∣ γ))