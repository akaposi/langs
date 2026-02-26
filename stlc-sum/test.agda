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
open import Cubical.Reflection.RecordEquiv hiding (_,_)
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path hiding (_,_)
open import Cubical.Data.Equality hiding (Iso; _≡_; funExt; _∙_; assoc; refl; sym; cong; id; step-≡;_∎)
module stlc-sum.test where
import stlc-sum.Syntax as S 
open import stlc-sum.InitialModel
open import stlc-sum.Weakening as W  using (Wk; Wk-emb; Wk-emb-∘; Wk-emb-id; Var; Var-emb)
open import stlc-sum.NormalForm as N using
    ( Ne; Nf; Discrete-Nf; Ne-emb; Nf-emb;
      _[_]ᴺᵉ; _[_]ᴺᶠ; Ne-emb-[]; Nf-emb-[]; []ᴺᵉ-∘; []ᴺᵉ-id; []ᴺᶠ-∘; []ᴺᶠ-id)
-- twisted gluing

import stlc-sum.DepModel as D
import stlc-sum.Induction

module test where
  private variable
    n : ℕ
    X Y Z P : S.Con
    Γˢ Δˢ : S.Con
    γˢ γ₁ˢ γ₂ˢ δˢ θˢ : S.Sub Δˢ Γˢ
    Aˢ Bˢ Cˢ : S.Ty
    aˢ a₁ˢ a₂ˢ bˢ cˢ fˢ tˢ : S.Tm Γˢ Aˢ

  record Con (Γˢ : S.Con) : Type₁ where
    no-eta-equality
    infixl 40 _[_]
    field
      ∣_∣ : S.Con → hSet lzero
      _[_] : fst ∣ X ∣ → Wk Y X → fst ∣ Y ∣
      ![]-∘ : ∀ γ (x : Wk Y X) (y : Wk Z Y) → γ [ x W.∘' y ] ≡ γ [ x ] [ y ]
      ![]-id : (γ : fst ∣ X ∣) → γ [ W.id' ] ≡ γ

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
      ∣_∣ : S.Con → hSet lzero
      _[_] : fst ∣ X ∣ → Wk Y X → fst ∣ Y ∣
      ![]-∘ : ∀ a (x : Wk Y X) (y : Wk Z Y) → a [ x W.∘' y ] ≡ (a [ x ] [ y ])
      ![]-id : (a : fst ∣ X ∣) → a [ W.id' ]  ≡ a

      map : fst ∣ X ∣ → S.Tm X Aˢ
      map-[] : ∀ a (x : Wk Y X) → map (a [ x ]) ≡ map a S.[ Wk-emb x ]

      quo : fst ∣ X ∣ → Nf X Aˢ
      quo-[] : ∀ a (x : Wk Y X) → quo (a [ x ]) ≡ quo a [ x ]ᴺᶠ
      emb-quo : (a : fst ∣ X ∣) → Nf-emb (quo a) ≡ map a

      ref : Ne X Aˢ → fst ∣ X ∣
      ref-[] : ∀ a (x : Wk Y X) → ref (a [ x ]ᴺᵉ) ≡ ref a [ x ]
      map-ref : (a : Ne X Aˢ) → map (ref a) ≡ Ne-emb a
  
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

  infixl 4 _,_
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
      sem  : Wk Y X → fst (∣ A ∣ Y)  → fst (∣ B ∣ Y) 
      ![] : ∀ (x : Wk Y X) a (y : Wk Z Y) → sem (x W.∘' y) (A ! a [ y ]) ≡ B ! sem x a [ y ] 
      map : ∀ (x : Wk Y X) a → B .map (sem x a) ≡ S.app (syn S.[ Wk-emb x ]) (A .map a)

  open Fun public

  Fun-is-set : isSet (Fun X A B)
  Fun-is-set = {!   !}

  Fun-path : ∀ {f₁ f₂ : Fun X A B} → 
    f₁ .syn ≡ f₂ .syn → 
    (∀ {Y} (x : Wk Y X)(a : fst (∣ A ∣ Y)) → f₁ .sem x a ≡ f₂ .sem x a) 
    → f₁ ≡ f₂ 
  Fun-path syn-path sem-path i .syn = syn-path i
  Fun-path syn-path sem-path i .sem x a = sem-path x a i
  Fun-path {X = X} {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .![] = isProp→PathP {B = λ i → ∀ {Z} {Y} (x : Wk Y X) a (y : Wk Z Y) → sem-path (x W.∘' y) (A ! a [ y ]) i ≡ B ! sem-path x a i [ y ]} (λ i₁ → isPropImplicitΠ2 λ X' Y' → isPropΠ3 λ w y' w' → snd (∣ B ∣ X') _ _) (f₁ .![]) (f₂ .![]) i
  Fun-path {X = X} {A = A} {B = B} {f₁ = f₁} {f₂ = f₂} syn-path sem-path i .map = isProp→PathP {B = λ i → ∀ {Y} (x : Wk Y X) a →  map B (sem-path x a i) ≡  S.app (syn-path i S.[ Wk-emb x ]) (map A a)} (λ i₁ → isPropImplicitΠ λ Y → isPropΠ2 λ w y → S.TmSet _ _) (f₁ .map) (f₂ .map) i

  infixr 0 _⇒_
  _⇒_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.⇒ Bˢ)
  ∣ A ⇒ B ∣ X = (Fun X A B) , Fun-is-set
  ((A ⇒ B) ! f [ x ]) .syn = f .syn S.[ Wk-emb x ]
  ((A ⇒ B) ! f [ x ]) .sem  = λ y a → f .sem (x W.∘' y) a
  ((A ⇒ B) ! f [ x ]) .![] y a z = (λ i → f .sem  (W.assoc' x y z i) (A ! a [ z ])) ∙ f .![] (x W.∘' y) a z
  ((A ⇒ B) ! f [ x ]) .map y a = f .map (x W.∘' y) a  ∙ (λ i → S.app (f .syn S.[ Wk-emb-∘ x y i ]) (map A a)) ∙ λ i → S.app (S.[]-∘ (f .syn) (Wk-emb x) (Wk-emb y) i) (map A a)
  (A ⇒ B) .![]-∘  f x y = Fun-path ((λ i → f .syn S.[ Wk-emb-∘ x y i ]) ∙ S.[]-∘ _ _ _) (λ z a → λ i → f .sem (sym (W.assoc' x y z) i) a)
  (A ⇒ B) .![]-id f = Fun-path ((λ i → f .syn S.[ Wk-emb-id i ]) ∙ S.[]-id _) (λ x a i → f .sem (W.idl' x i) a)
  (A ⇒ B) .map = syn
  (A ⇒ B) .map-[] f x = refl
  (A ⇒ B) .quo f = Nf.lam (B .quo (f .sem (W.id' W.∘p) (A .ref (N.var W.q))))
  (A ⇒ B) .quo-[]  f x = (λ i → Nf.lam (quo B ((f .sem ((W.idr' x ∙ sym (W.idl' x)) i Wk.∘p) (A .ref-[] (Ne.var Var.q) (x Wk.↑') i))))) 
                          ∙ (λ i → Nf.lam (quo B (f .![] (W.id' Wk.∘p) (ref A (Ne.var Var.q)) (x Wk.↑') i))) ∙ λ i → Nf.lam ((B .quo-[] (f .sem (W.id' Wk.∘p) (ref A (Ne.var Var.q))) (x Wk.↑') i))
  (A ⇒ B) .emb-quo f = (λ i → S.lam (B .emb-quo (f .sem (W.id' Wk.∘p) (A .ref (Ne.var W.q))) i)) ∙ (λ i → S.lam (f .map (W.id' Wk.∘p) (ref A (Ne.var Var.q)) i)) ∙ (λ i → S.lam (S.app (f .syn S.[ Wk-emb-id i S.∘ S.p ]) ((A .map (A .ref (Ne.var W.q)))))) ∙ (λ i → S.lam (S.app (f .syn S.[ S.idl S.p i ]) (A .map-ref (Ne.var Var.q) i))) ∙ S.⇒-η (f .syn)

  (A ⇒ B) .ref f .syn = Ne-emb f
  (A ⇒ B) .ref f .sem x a = B .ref (N.app (f [ x ]ᴺᵉ) (A .quo a))
  (A ⇒ B) .ref f .![]  x a y = ((λ i → ref B (Ne.app ([]ᴺᵉ-∘ f x y i) (quo A (A ! a [ y ])))) ∙ λ i →  ref B (Ne.app (f [ x ]ᴺᵉ [ y ]ᴺᵉ) (A .quo-[] a y i))) ∙ B .ref-[] _ _
  (A ⇒ B) .ref f .map x a = B .map-ref (Ne.app (f [ x ]ᴺᵉ) (quo A a)) ∙ (λ i → S.app (Ne-emb-[] f x i) (Nf-emb (A .quo a))) ∙ λ i → S.app (Ne-emb f S.[ Wk-emb x ]) (A .emb-quo a i)
  (A ⇒ B) .ref-[] f x = Fun-path (Ne-emb-[] f x) (λ y a i → ref B (Ne.app ([]ᴺᵉ-∘ f x y (~ i)) (quo A a)))
  (A ⇒ B) .map-ref f = refl

  app : Tm Γ (A ⇒ B) fˢ → Tm Γ A aˢ → Tm Γ B (S.app fˢ aˢ)
  ∣ app f a ∣ γ = ( ∣ f ∣ γ )  .sem W.id' (∣ a ∣ γ)
  app {Γ = Γ} {A = A} {B = B} f a .![] γ x =  (λ i → f .![] γ x i .sem W.id' (∣ a ∣ (Γ ! γ [ x ]))) ∙ (λ i → ∣ f ∣ γ .sem  (W.idr' x i) (∣ a ∣ (Γ ! γ [ x ]))) ∙ (λ i → ∣ f ∣ γ .sem (W.idl' x (~ i)) (a .![] γ x i)) ∙ ∣ f ∣ γ .![] W.id' (∣ a ∣ γ) x 
  app  {Γ = Γ} {A = A} {B = B} {fˢ = fˢ} {aˢ = aˢ} f a .map γ = (∣ f ∣ γ .map W.id' (∣ a ∣ γ)) ∙ (λ i → S.app (∣ f ∣ γ .syn S.[ Wk-emb-id i ]) (map A (∣ a ∣ γ))) ∙ (λ i → S.app (S.[]-id (∣ f ∣ γ .syn) i) (A .map (∣ a ∣ γ))) ∙ (λ i →  S.app ((f .map γ) i) ((a .map γ) i)) ∙ sym (S.app-[] fˢ aˢ (map Γ γ))

  app-[] :
    (f : Tm Γ (A ⇒ B) fˢ) (a : Tm Γ A aˢ) (γ : Sub Δ Γ γˢ) →
    app f a [ γ ] ≡ᵗ[ S.app-[] _ _ _ ] app (f [ γ ]) (a [ γ ])
  app-[] f a γ = Tm-path λ δ → refl


  lam : Tm (Γ ▸ A) B bˢ → Tm Γ (A ⇒ B) (S.lam bˢ)
  ∣ lam {Γ = Γ} {bˢ = bˢ} b ∣ γ .syn = S.lam bˢ S.[ Γ .map γ ]
  ∣ lam {Γ = Γ} b ∣ γ .sem x a = ∣ b ∣ ((Γ ! γ [ x ]) , a)
  ∣ lam {Γ = Γ} {A = A} {B = B} b ∣ γ .![] x a y = (λ i → ∣ b ∣ ((Γ .![]-∘ γ x y i) , (A ! a [ y ]))) ∙ b .![] (Γ ! γ [ x ] , a) y
  ∣ lam {Γ = Γ} {A = A} {B = B} {bˢ = bˢ} b ∣ γ .map x a = b .map (Γ ! γ [ x ] , a) ∙ {!   !}
  lam {Γ = Γ} {bˢ = bˢ} b .![] γ x = Fun-path 
    ((λ i → (S.lam bˢ S.[ Γ .map-[] γ x i ])) ∙ S.[]-∘ (S.lam bˢ)  (Γ .map γ) (Wk-emb x)) 
    λ x₁ a i → ∣ b ∣ ((Γ .![]-∘ γ x x₁ (~ i)) , a)
  lam b .map γ = refl 

  lam-[] :
    (b : Tm (Γ ▸ A) B bˢ) (γ : Sub Δ Γ γˢ) →
    lam b [ γ ] ≡ᵗ[ S.lam-[] _ _ ] lam (b [ γ ↑ ])
  lam-[] {Γ = Γ} {bˢ = bˢ} {Δ = Δ} {γˢ = γˢ} b γ = Tm-path (λ δ → Fun-path ((λ i → S.lam bˢ S.[ γ .map δ i ]) ∙ S.[]-∘ (S.lam bˢ) γˢ (map Δ δ) ∙ λ i → (S.lam-[] bˢ γˢ i S.[ map Δ δ ])  ) (λ x a i → ∣ b ∣ ((γ .![] δ x (~ i)) , a)))

  ⇒-β :
    (b : Tm (Γ ▸ A) B bˢ) (a : Tm Γ A aˢ) →
    app (lam b) a ≡ᵗ[ S.⇒-β _ _ ] b [ ⟨ a ⟩ ]
  ⇒-β {Γ = Γ} b a = Tm-path λ γ i → ∣ b ∣ ((Γ .![]-id γ i) , (∣ a ∣ γ)) 

  ⇒-η : (f : Tm Γ (A ⇒ B) fˢ) → lam (app (f [ p ]) q) ≡ᵗ[ S.⇒-η _ ] f
  ⇒-η {Γ = Γ} {fˢ = fˢ} f = Tm-path λ γ → 
    Fun-path ((λ i → S.⇒-η fˢ i S.[ map Γ γ ]) ∙ sym (f .map γ)) 
    λ x a  → (λ i → f .![] γ x i .sem  W.id' a) ∙ λ i → ∣ f ∣ γ .sem  (W.idr' x i) a  

  _+ₗ_ : Ty Aˢ → Ty Bˢ → Ty (Aˢ S.+ₗ Bˢ) 
  ∣ _+ₗ_ {Aˢ} {Bˢ} A B ∣ Γ = (Ne Γ (Aˢ S.+ₗ Bˢ) ⊎ (fst (∣ A ∣ Γ) ⊎ fst (∣ B ∣ Γ))) , isSet⊎ N.isNeSet (isSet⊎ (snd (∣ A ∣ Γ)) (snd (∣ B ∣ Γ)))
  _+ₗ_ {Aˢ} {Bˢ} A B ! inl n [ x ] = inl (n [ x ]ᴺᵉ)
  _+ₗ_ {Aˢ} {Bˢ} A B ! inr (inl a) [ x ] = inr (inl (A ._!_[_] a x)) 
  _+ₗ_ {Aˢ} {Bˢ} A B ! inr (inr b) [ x ] = inr (inr (B ._!_[_] b x))
  _+ₗ_ {Aˢ} {Bˢ} A B .![]-∘ (inl n) x y = λ i → inl ([]ᴺᵉ-∘ n x y i)
  _+ₗ_ {Aˢ} {Bˢ} A B .![]-∘ (inr (inl a)) x y = λ i → inr (inl (A .![]-∘ a x y i))
  _+ₗ_ {Aˢ} {Bˢ} A B .![]-∘ (inr (inr b)) x y = λ i → inr (inr (B .![]-∘ b x y i)) 
  _+ₗ_ {Aˢ} {Bˢ} A B .![]-id (inl s) = λ i → inl ([]ᴺᵉ-id s i)
  _+ₗ_ {Aˢ} {Bˢ} A B .![]-id (inr (inl a)) = λ i → inr (inl (A .![]-id a i))
  _+ₗ_ {Aˢ} {Bˢ} A B .![]-id (inr (inr b)) = λ i → inr (inr (B .![]-id b i))
  _+ₗ_ {Aˢ} {Bˢ} A B .map (inl x) = Ne-emb x
  _+ₗ_ {Aˢ} {Bˢ} A B .map (inr (inl a)) = S.inlₗ (A .map a)
  _+ₗ_ {Aˢ} {Bˢ} A B .map (inr (inr b)) = S.inrₗ (B .map b)
  _+ₗ_ {Aˢ} {Bˢ} A B .map-[] (inl s) x = Ne-emb-[] s x
  _+ₗ_ {Aˢ} {Bˢ} A B .map-[] (inr (inl a)) x = (λ i → S.inlₗ (A .map-[] a x i)) ∙ sym (S.inlₗ-[] (map A a) (Wk-emb x))
  _+ₗ_ {Aˢ} {Bˢ} A B .map-[] (inr (inr b)) x = (λ i → S.inrₗ (B .map-[] b x i)) ∙ sym (S.inrₗ-[] (map B b) (Wk-emb x))
  _+ₗ_ {Aˢ} {Bˢ} A B .quo (inl s) = N.+-ne s
  _+ₗ_ {Aˢ} {Bˢ} A B .quo (inr (inl a)) = N.inlₗ (A .quo a)
  _+ₗ_ {Aˢ} {Bˢ} A B .quo (inr (inr b)) = N.inrₗ (B .quo b)
  _+ₗ_ {Aˢ} {Bˢ} A B .quo-[] (inl s) x = refl
  _+ₗ_ {Aˢ} {Bˢ} A B .quo-[] (inr (inl a)) x = λ i → Nf.inlₗ (A .quo-[] a x i)
  _+ₗ_ {Aˢ} {Bˢ} A B .quo-[] (inr (inr b)) x = λ i → Nf.inrₗ (B .quo-[] b x i)
  _+ₗ_ {Aˢ} {Bˢ} A B .emb-quo (inl s) = refl
  _+ₗ_ {Aˢ} {Bˢ} A B .emb-quo (inr (inl a)) = λ i → S.inlₗ (A .emb-quo a i)
  _+ₗ_ {Aˢ} {Bˢ} A B .emb-quo (inr (inr b)) = λ i → S.inrₗ (B .emb-quo b i)
  _+ₗ_ {Aˢ} {Bˢ} A B .ref s = inl s
  _+ₗ_ {Aˢ} {Bˢ} A B .ref-[] s x = refl
  _+ₗ_ {Aˢ} {Bˢ} A B .map-ref s = refl

  inlₗ : Tm Γ A aˢ → Tm Γ (A +ₗ B) (S.inlₗ aˢ)
  ∣ inlₗ {Γ = Γ} {A = A} a ∣ x = inr (inl (∣ a ∣ x))
  inlₗ a .![] x w = λ i → inr (inl (a .![] x w i))
  inlₗ {Γ = Γ} {aˢ = aˢ} a .map x = (λ i → S.inlₗ (a .map x i)) ∙  sym (S.inlₗ-[]  aˢ (map Γ x))

  inlₗ-[] : (a : Tm Γ A aˢ)(γ : Sub Δ Γ γˢ) →  inlₗ {B = B} a [ γ ] ≡ᵗ[ S.inlₗ-[] aˢ γˢ ] inlₗ {B = B}  (a [ γ ])
  inlₗ-[] a γ = Tm-path λ δ → refl
  
  inrₗ : Tm Γ B bˢ → Tm Γ (A +ₗ B) (S.inrₗ bˢ)
  ∣ inrₗ b ∣ x = inr (inr (∣ b ∣ x))
  inrₗ b .![] x w = λ i → inr (inr (b .![] x w i))
  inrₗ {Γ = Γ} {bˢ = bˢ} b .map x = (λ i → S.inrₗ (b .map x i)) ∙  sym (S.inrₗ-[]  bˢ (map Γ x))   
  
  inrₗ-[] : (b : Tm Γ B bˢ)(γ : Sub Δ Γ γˢ) →  inrₗ {A = A} b [ γ ] ≡ᵗ[ S.inrₗ-[] bˢ γˢ ] inrₗ {A = A}  (b [ γ ])
  inrₗ-[] a γ = Tm-path λ δ → refl

  case+-sem : {Aˢ Bˢ : S.Ty}(A : Ty Aˢ)(B : Ty Bˢ)(C : Ty Cˢ) →  N.Ne X (Aˢ S.+ₗ Bˢ) ⊎ (fst (∣ A ∣ X) ⊎ fst (∣ B ∣ X)) 
             → (∀ {Y} → Wk Y X → fst (∣ A ∣ Y) → fst (∣ C ∣ Y)) → (∀ {Y} → Wk Y X → fst (∣ B ∣ Y) → fst (∣ C ∣ Y))  → fst (∣ C ∣ X) 
  case+-sem A B C (inl x) fa fb = C .ref (N.case x (C .quo (fa (W._∘p W.id') (A .ref (Ne.var W.q)))) (C .quo (fb (W._∘p W.id') (B .ref (Ne.var W.q)))))
  case+-sem A B C (inr (inl a)) fa fb = fa W.id' a
  case+-sem A B C (inr (inr b)) fa fb = fb W.id' b

  case+ : Tm Γ (A +ₗ B) cˢ → Tm (Γ ▸ A) C aˢ → Tm (Γ ▸ B) C bˢ → Tm Γ C (S.case+ cˢ aˢ bˢ)
  ∣ case+ {Γ = Γ} {A = A} {B = B} {C = C} c a' b' ∣ γ = case+-sem A B C (∣ c ∣ γ) (λ x a → ∣ a' ∣ (Con._[_] Γ γ x , a)) λ x b → ∣ b' ∣ ((Con._[_] Γ γ x) , b) 
  case+ {Γ = Γ} {A = A} {B = B} {C = C} c a b .![] γ x = 
    case+-sem A B C (∣ c ∣ (Γ ! γ [ x ])) (λ x₁ a₁ → ∣ a ∣ (Γ ! Γ ! γ [ x ] [ x₁ ] , a₁)) (λ x₁ b₁ → ∣ b ∣ (Γ ! Γ ! γ [ x ] [ x₁ ] , b₁))  ≡⟨  (λ i → case+-sem A B C (c .![] γ x i) (λ x₁ a₁ → ∣ a ∣ (Γ ! Γ ! γ [ x ] [ x₁ ] , a₁)) (λ x₁ b₁ → ∣ b ∣ (Γ ! Γ ! γ [ x ] [ x₁ ] , b₁))) ⟩
    case+-sem A B C ((A +ₗ B) ! ∣ c ∣ γ [ x ])
      (λ x₁ a₁ → ∣ a ∣ ((Con._[_] Γ (Con._[_] Γ γ x) x₁) , a₁))
      (λ x₁ b₁ → ∣ b ∣ ((Con._[_] Γ (Con._[_] Γ γ x) x₁) , b₁))  ≡⟨ case+-![]  (∣ c ∣ γ) ⟩
    C ! ∣ case+ c a b ∣ γ [ x ] ∎
      where 
        case+-![] : ∀ vc → case+-sem A B C ((A +ₗ B) ! vc [ x ])  (λ x₁ a₁ → ∣ a ∣ ((Con._[_] Γ (Con._[_] Γ γ x) x₁) , a₁)) (λ x₁ b₁ → ∣ b ∣ ((Con._[_] Γ (Con._[_] Γ γ x) x₁) , b₁)) ≡ C ._!_[_] (case+-sem A B C vc  (λ x₁ a₁ → ∣ a ∣ (Con._[_] Γ γ x₁ , a₁)) (λ x₁ b₁ → ∣ b ∣ (Con._[_] Γ γ x₁ , b₁))) x
        case+-![] (inl n) = 
          let 
            eqΓ : Con._[_] Γ γ (x W.∘' (W.id' Wk.∘p)) ≡ (Γ ! Con._[_] Γ γ (W.id' Wk.∘p) [ (x Wk.↑') ]) 
            eqΓ = (λ i → Γ ! γ [ W.idr' x i  Wk.∘p ]) ∙ (λ i → Γ ! γ [ W.idl' x (~ i)  Wk.∘p ]) ∙  Γ .![]-∘  γ (W.id' Wk.∘p) (x Wk.↑')
            eqΓ' : Con._[_] Γ γ (x W.∘' (W.id' Wk.∘p)) ≡ (Γ ! Con._[_] Γ γ (W.id' Wk.∘p) [ (x Wk.↑') ]) 
            eqΓ' = (λ i → Γ ! γ [ W.idr' x i  Wk.∘p ]) ∙ (λ i → Γ ! γ [ W.idl' x (~ i)  Wk.∘p ]) ∙  Γ .![]-∘  γ (W.id' Wk.∘p) (x Wk.↑') -- generalize
            eqa : ref A (Ne.var Var.q) ≡ A ._!_[_] ( ref A (Ne.var Var.q)) (x Wk.↑')
            eqa = (A .ref-[] (Ne.var Var.q) (x Wk.↑'))
            eqb : ref B (Ne.var Var.q) ≡ B ._!_[_] ( ref B (Ne.var Var.q)) (x Wk.↑')
            eqb = (B .ref-[] (Ne.var Var.q) (x Wk.↑'))
          in 
          (λ i → ref C (Ne.case (n [ x ]ᴺᵉ) (quo C (∣ a ∣ (Γ .![]-∘ γ  x (W.id' Wk.∘p) (~ i) , ref A (Ne.var Var.q)))) (quo C (∣ b ∣ (Γ .![]-∘ γ  x (W.id' Wk.∘p) (~ i) , ref B (Ne.var Var.q)))))) 
          ∙ (λ i → ref C ((Ne.case (n [ x ]ᴺᵉ) (quo C (∣ a ∣ ((eqΓ i) , (eqa  i)))) (quo C (∣ b ∣ (eqΓ' i , (eqb i))))))) 
          ∙ (λ i → ref C ((Ne.case (n [ x ]ᴺᵉ) (quo C (a .![] ((Γ ! γ [ W.id' Wk.∘p ]) , ref A (Ne.var Var.q)) (x Wk.↑') i)) (quo C (b .![] ((Γ ! γ [ W.id' Wk.∘p ]) , ref B (Ne.var Var.q)) (x Wk.↑') i)))))
          ∙ (λ i → ref C ((Ne.case (n [ x ]ᴺᵉ) (C .quo-[] (∣ a ∣ ((Γ ! γ [ W.id' Wk.∘p ]) , ref A (Ne.var Var.q))) (x Wk.↑') i) (C .quo-[] (∣ b ∣ ((Γ ! γ [ W.id' Wk.∘p ]) , ref B (Ne.var Var.q))) (x Wk.↑') i))))   
          ∙ (C .ref-[] 
              (Ne.case n 
                (quo C (∣ a ∣ (Γ ! γ [ W.id' Wk.∘p ] , ref A (Ne.var Var.q)))) 
                (quo C (∣ b ∣ (Γ ! γ [ W.id' Wk.∘p ] , ref B (Ne.var Var.q))))) 
              x)
        case+-![] (inr (inl va)) = (λ i → ∣ a ∣ (Γ .![]-id (Γ ! γ [ x ]) i , A ! va [ x ]))  ∙ (λ i →  ∣ a ∣ (Γ ! Γ .![]-id γ (~ i) [ x ] , A ! va [ x ]))  ∙ a .![] _ _
        case+-![] (inr (inr vb)) = (λ i → ∣ b ∣ (Γ .![]-id (Γ ! γ [ x ]) i , B ! vb [ x ]))  ∙ (λ i →  ∣ b ∣ (Γ ! Γ .![]-id γ (~ i) [ x ] , B ! vb [ x ]))  ∙ b .![] _ _
        
  case+ {Γ = Γ}{A = A}{B = B}{cˢ = cˢ}{C = C}{aˢ =  aˢ}{bˢ = bˢ} c a b .map γ =
    C .map  (case+-sem A B C (∣ c ∣ γ) (λ x a' → ∣ a ∣ ((Con._[_] Γ γ x) , a')) λ x b' → ∣ b ∣ ( (Con._[_] Γ γ x), b'))  ≡⟨ case+-map (∣ c ∣ γ) ⟩
    S.case+ (map (A +ₗ B) (∣ c ∣ γ)) (aˢ S.[ map Γ γ S.↑ ]) (bˢ S.[ map Γ γ S.↑ ])            ≡⟨ (λ i → S.case+ (c .map γ i) (aˢ S.[ map Γ γ S.↑ ]) (bˢ S.[ map Γ γ S.↑ ])) ⟩
    S.case+ (cˢ S.[ map Γ γ ]) (aˢ S.[ map Γ γ S.↑ ]) (bˢ S.[ map Γ γ S.↑ ]) ≡⟨ sym (S.case+[] _ _ _ _) ⟩
    (S.case+ cˢ aˢ bˢ S.[ map Γ γ ]) ∎
      where
        case+-map : ∀ vc → 
                    C .map (case+-sem A B C vc 
                             (λ x a' → ∣ a ∣ (Con._[_] Γ γ x , a')) 
                             (λ x b' → ∣ b ∣ (Con._[_] Γ γ x , b'))) 
                    ≡ S.case+ (map (A +ₗ B) vc) (aˢ S.[ map Γ γ S.↑ ]) (bˢ S.[ map Γ γ S.↑ ])
        case+-map (inl x) = C .map-ref _ ∙ (λ i → S.case+ (Ne-emb x) (C .emb-quo
           (∣ a ∣ ((Γ ! γ [ W.id' Wk.∘p ]) , ref A (Ne.var Var.q))) i) (C .emb-quo
              (∣ b ∣ ((Γ ! γ [ W.id' Wk.∘p ]) , ref B (Ne.var Var.q))) i)) 
              ∙ (λ i → S.case+ (Ne-emb x) (a .map (Con._[_] Γ γ (W.id' Wk.∘p) , A .ref (Ne.var Var.q)) i) (b .map (Con._[_] Γ γ (W.id' Wk.∘p) , B .ref (Ne.var Var.q)) i)) 
              ∙ (λ i → S.case+ (Ne-emb x) (aˢ S.[ Γ .map-[] γ (W.id' Wk.∘p) i S., A .map-ref (Ne.var Var.q) i ]) (bˢ S.[ Γ .map-[] γ (W.id' Wk.∘p) i S., B .map-ref (Ne.var Var.q) i ])) 
              ∙ (λ i → S.case+ (Ne-emb x) (aˢ S.[ map Γ γ S.∘ (Wk-emb-id i S.∘ S.p) S., S.q ]) (bˢ S.[ map Γ γ S.∘ (Wk-emb-id i S.∘ S.p) S., S.q ])) 
              ∙ λ i → S.case+ (Ne-emb x) (aˢ S.[ map Γ γ S.∘ S.idl S.p i S., S.q ]) (bˢ S.[ map Γ γ S.∘ S.idl S.p i S., S.q ])
        case+-map (inr (inl va)) = 
          let 
            envA = (Con._[_] Γ γ W.id' , va)
          in 
          a .map envA
          ∙ (λ i → aˢ S.[ Γ .map-[] γ W.id' i S., map A va ])
          ∙ (λ i → aˢ S.[ map Γ γ S.∘ Wk-emb-id i S., map A va ])
          ∙ (λ i → aˢ S.[ map Γ γ S.∘ S.▸-β₁ S.id (map A va) (~ i) S., map A va ])
          ∙ (λ i → aˢ S.[ S.assoc (map Γ γ) (S.p ) (S.id S., map A va) i S., map A va ])
          ∙ (λ i → aˢ S.[ map Γ γ S.∘ S.p S.∘ (S.id S., map A va) S., S.▸-β₂ S.id  (map A va) (~ i) ])
          ∙ (λ i → aˢ S.[ S.,-∘ (map Γ γ S.∘ S.p) S.q (S.id S., map A va) (~ i) ])
          ∙ S.[]-∘ aˢ (map Γ γ S.∘ S.p S., S.q) (S.id S., map A va)
          ∙ sym (S.+-β₁ (map A va) (aˢ S.[ map Γ γ S.↑ ]) (bˢ S.[ map Γ γ S.↑ ]))
        case+-map (inr (inr vb)) = 
          let 
            envB = (Con._[_] Γ γ W.id' , vb)
          in 
          b .map envB
          ∙ (λ i → bˢ S.[ Γ .map-[] γ W.id' i S., map B vb ])
          ∙ (λ i → bˢ S.[ map Γ γ S.∘ Wk-emb-id i S., map B vb ]) 
          ∙ (λ i → bˢ S.[ map Γ γ S.∘ S.▸-β₁ S.id (map B vb) (~ i) S., map B vb ])
          ∙ (λ i → bˢ S.[ S.assoc (map Γ γ) (S.p ) (S.id S., map B vb) i S., map B vb ])
          ∙ (λ i → bˢ S.[ map Γ γ S.∘ S.p S.∘ (S.id S., map B vb) S., S.▸-β₂ S.id  (map B vb) (~ i) ])
          ∙ (λ i → bˢ S.[ S.,-∘ (map Γ γ S.∘ S.p) S.q (S.id S., map B vb) (~ i) ])
          ∙ S.[]-∘ bˢ (map Γ γ S.∘ S.p S., S.q) (S.id S., map B vb)
          ∙ sym (S.+-β₂ (map B vb) ((aˢ S.[ map Γ γ S.↑ ])) (bˢ S.[ map Γ γ S.↑ ]))            
              
  case+[] : (t : Tm Γ (A +ₗ B) cˢ)(a : Tm (Γ ▸ A) C aˢ)(b : Tm (Γ ▸ B) C bˢ)(γ : Sub Δ Γ γˢ) → case+ t a b [ γ ] ≡ᵗ[ S.case+[] cˢ aˢ bˢ γˢ ] case+ (t [ γ ]) (a [ γ ↑ ]) (b [ γ ↑ ])
  case+[] {A = A} {B = B} {C = C} t a b γ = Tm-path (λ x → λ i → case+-sem A B C (∣ t ∣ (∣ γ ∣ x)) (λ w y → ∣ a ∣ (sym (γ .![] x w) i  , y)) (λ w y → ∣ b ∣ (sym (γ .![] x w) i  , y))) 
   
  +-β₁ : (t : Tm Γ A tˢ)(a : Tm (Γ ▸ A) C aˢ)(b : Tm (Γ ▸ B) C bˢ) → case+ (inlₗ  t) a b ≡ᵗ[ S.+-β₁ tˢ aˢ bˢ ]  (a [ id , t ₛ ]) 
  +-β₁ {Γ = Γ} t a b = Tm-path (λ γ i → ∣ a ∣ (Γ .![]-id γ i , ∣ t ∣ γ))

  +-β₂ : (t : Tm Γ B tˢ)(a : Tm (Γ ▸ A) C aˢ)(b : Tm (Γ ▸ B) C bˢ) → case+ (inrₗ {A = A} t) a b  ≡ᵗ[ S.+-β₂ tˢ aˢ bˢ ] (b [ id , t ₛ ]) 
  +-β₂ {Γ = Γ} t a b = Tm-path (λ γ i → ∣ b ∣ (Γ .![]-id γ i , ∣ t ∣ γ))

  ⊥ₗ : Ty S.⊥ₗ 
  ∣ ⊥ₗ ∣ Γ = Nf Γ S.⊥ₗ , N.isNfSet
  ⊥ₗ ._!_[_] = _[_]ᴺᶠ
  ⊥ₗ .![]-∘ = []ᴺᶠ-∘
  ⊥ₗ .![]-id = []ᴺᶠ-id
  ⊥ₗ .map = Nf-emb
  ⊥ₗ .map-[] = Nf-emb-[]
  ⊥ₗ .quo t = t
  ⊥ₗ .quo-[] t x  = refl
  ⊥ₗ .emb-quo t = refl
  ⊥ₗ .ref = N.⊥ₗ-ne
  ⊥ₗ .ref-[] t x = refl
  ⊥ₗ .map-ref t = refl

  exfalso-sem : (A : Ty Aˢ) → Nf X S.⊥ₗ → fst ( ∣ A ∣ X )
  exfalso-sem A (N.⊥ₗ-ne t) = A .ref (N.exfalsoₗ t)

  exfalsoₗ : Tm Γ ⊥ₗ tˢ → Tm Γ A (S.exfalsoₗ tˢ)
  ∣ exfalsoₗ {A = A} t ∣ γ = exfalso-sem A (∣ t ∣  γ)
  exfalsoₗ {Γ = Γ} {A = A} t .![] γ x' = (λ i → exfalso-sem A (t .![] γ x' i)) ∙ exfalsoₗ-![] (∣ t ∣ γ)
    where 
      exfalsoₗ-![] : ∀ t → exfalso-sem A (t [ x' ]ᴺᶠ) ≡ A ! exfalso-sem A t [ x' ]
      exfalsoₗ-![] (N.⊥ₗ-ne x) = A .ref-[] (Ne.exfalsoₗ x) x'
  exfalsoₗ {Γ = Γ} {tˢ = tˢ} {A = A} t .map γ = (exfalsoₗ-map (∣ t ∣  γ) ∙ (λ i → S.exfalsoₗ  (t .map γ i))) ∙  sym (S.exfalsoₗ-[] _ _)
    where
      exfalsoₗ-map : ∀ t → A .map (exfalso-sem A t) ≡ S.exfalsoₗ (Nf-emb t)
      exfalsoₗ-map (N.⊥ₗ-ne x) = A .map-ref _

  exfalsoₗ-[] : (t : Tm Γ ⊥ₗ tˢ) (γ : Sub Δ Γ γˢ) → exfalsoₗ {A = A} t [ γ ] ≡ᵗ[ S.exfalsoₗ-[] _ _ ] exfalsoₗ (t [ γ ])
  exfalsoₗ-[] t γ = Tm-path λ δ → refl

  Unitₗ :  Ty S.Unitₗ
  ∣ Unitₗ ∣ X = Nf X S.Unitₗ , N.isNfSet
  Unitₗ ._!_[_] = _[_]ᴺᶠ
  Unitₗ .![]-∘ = []ᴺᶠ-∘
  Unitₗ .![]-id = []ᴺᶠ-id
  Unitₗ .map = Nf-emb
  Unitₗ .map-[] = Nf-emb-[]
  Unitₗ .quo t = t
  Unitₗ .quo-[] t x = refl
  Unitₗ .emb-quo t = refl
  Unitₗ .ref n = Nf.ttₗ
  Unitₗ .ref-[] ttₗ x = refl 
  Unitₗ .map-ref ttₗ = λ i → S.unit-η (Ne-emb ttₗ) (~ i)

  ttₗ :  Tm Γ Unitₗ S.ttₗ
  ∣ ttₗ ∣ X = Nf.ttₗ
  ttₗ .![] γ x = refl
  ttₗ {Γ = Γ} .map γ = sym (S.ttₗ-[] (map Γ γ)) 


  ttₗ-[] : (γ : Sub Δ Γ γˢ) → ttₗ [ γ ]  ≡ᵗ[ S.ttₗ-[] _ ] ttₗ 
  ttₗ-[] γ = Tm-path λ δ → refl

  unit-η : ∀ {Γ} (t : Tm Γ Unitₗ tˢ) → t ≡ᵗ[ S.unit-η tˢ ] ttₗ
  unit-η {tˢ = tˢ} t = Tm-path λ γ → unit-nf-unique (∣ t ∣ γ)
    where
      unit-nf-unique : ∀ {Γ} (n : Nf Γ S.Unitₗ) → n ≡ Nf.ttₗ
      unit-nf-unique Nf.ttₗ = refl
      