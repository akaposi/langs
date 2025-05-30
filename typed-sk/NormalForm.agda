{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Function
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ)
open import Agda.Builtin.Unit
import typed-sk.Syntax as I


module typed-sk.NormalForm where


data Nf : (T : I.Ty) → I.Tm T → Type 
  
data Nf where
  K₀ : ∀{A B} → Nf (A I.⇒ (B I.⇒ A)) I.K 
  K₁ : ∀{A B t} → Nf A t → Nf (B I.⇒ A) (I.K I.· t) 
  S₀ : ∀{A B C} → Nf ((A I.⇒ B I.⇒ C) I.⇒ (A I.⇒ B) I.⇒ A I.⇒ C) I.S
  S₁ : ∀{A B C t} → Nf (A I.⇒ B I.⇒ C) t → Nf ((A I.⇒ B) I.⇒ A I.⇒ C) (I.S I.· t) 
  S₂ : ∀{A B C t u} → Nf (A I.⇒ B I.⇒ C) t → Nf (A I.⇒ B) u → Nf (A I.⇒ C) (I.S I.· t I.· u) 

hDisjK₀ : (Σ I.Ty λ A → Σ (I.Tm A) λ t → Nf A t) → Type
hDisjK₀ (.(_ I.⇒ _ I.⇒ _) , .I.K , K₀) = ⊤
hDisjK₀ (.(_ I.⇒ _) , .(I.K I.· _) , K₁ n) = ⊥
hDisjK₀ (.((_ I.⇒ _ I.⇒ _) I.⇒ (_ I.⇒ _) I.⇒ _ I.⇒ _) , .I.S , S₀) = ⊥
hDisjK₀ (.((_ I.⇒ _) I.⇒ _ I.⇒ _) , .(I.S I.· _) , S₁ n) = ⊥
hDisjK₀ (.(_ I.⇒ _) , .(I.S I.· _ I.· _) , S₂ n n₁) = ⊥

hDisjK₁ : (Σ I.Ty λ A → Σ (I.Tm A) λ t → Nf A t) → Type
hDisjK₁ (.(_ I.⇒ _ I.⇒ _) , .I.K , K₀) = ⊥
hDisjK₁ (.(_ I.⇒ _) , .(I.K I.· _) , K₁ n) = ⊤
hDisjK₁ (.((_ I.⇒ _ I.⇒ _) I.⇒ (_ I.⇒ _) I.⇒ _ I.⇒ _) , .I.S , S₀) = ⊥
hDisjK₁ (.((_ I.⇒ _) I.⇒ _ I.⇒ _) , .(I.S I.· _) , S₁ n) = ⊥
hDisjK₁ (.(_ I.⇒ _) , .(I.S I.· _ I.· _) , S₂ n n₁) = ⊥

hDisjS₀ : (Σ I.Ty λ A → Σ (I.Tm A) λ t → Nf A t) → Type
hDisjS₀ (.(_ I.⇒ _ I.⇒ _) , .I.K , K₀) = ⊥
hDisjS₀ (.(_ I.⇒ _) , .(I.K I.· _) , K₁ n) = ⊥
hDisjS₀ (.((_ I.⇒ _ I.⇒ _) I.⇒ (_ I.⇒ _) I.⇒ _ I.⇒ _) , .I.S , S₀) = ⊤
hDisjS₀ (.((_ I.⇒ _) I.⇒ _ I.⇒ _) , .(I.S I.· _) , S₁ n) = ⊥
hDisjS₀ (.(_ I.⇒ _) , .(I.S I.· _ I.· _) , S₂ n n₁) = ⊥

hDisjS₁ : (Σ I.Ty λ A → Σ (I.Tm A) λ t → Nf A t) → Type
hDisjS₁ (.(_ I.⇒ _ I.⇒ _) , .I.K , K₀) = ⊥
hDisjS₁ (.(_ I.⇒ _) , .(I.K I.· _) , K₁ n) = ⊥
hDisjS₁ (.((_ I.⇒ _ I.⇒ _) I.⇒ (_ I.⇒ _) I.⇒ _ I.⇒ _) , .I.S , S₀) = ⊥
hDisjS₁ (.((_ I.⇒ _) I.⇒ _ I.⇒ _) , .(I.S I.· _) , S₁ n) = ⊤
hDisjS₁ (.(_ I.⇒ _) , .(I.S I.· _ I.· _) , S₂ n n₁) = ⊥

hDisjS₂ : (Σ I.Ty λ A → Σ (I.Tm A) λ t → Nf A t) → Type
hDisjS₂ (.(_ I.⇒ _ I.⇒ _) , .I.K , K₀) = ⊥
hDisjS₂ (.(_ I.⇒ _) , .(I.K I.· _) , K₁ n) = ⊥
hDisjS₂ (.((_ I.⇒ _ I.⇒ _) I.⇒ (_ I.⇒ _) I.⇒ _ I.⇒ _) , .I.S , S₀) = ⊥
hDisjS₂ (.((_ I.⇒ _) I.⇒ _ I.⇒ _) , .(I.S I.· _) , S₁ n) = ⊥
hDisjS₂ (.(_ I.⇒ _) , .(I.S I.· _ I.· _) , S₂ n n₁) = ⊤

K₀-cong : ∀{A₀ A₁ B₀ B₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ A₀ , I.K , K₀ {A₀}{B₀}) (A₁ I.⇒ B₁ I.⇒ A₁ , I.K , K₀ {A₁}{B₁})
K₀-cong a b = λ i → ((a i) I.⇒ (b i) I.⇒ (a i)) , (I.K , K₀)
K₀-inj₀ : ∀{A₀ A₁ B₀ B₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ A₀ , I.K , K₀ {A₀}{B₀}) (A₁ I.⇒ B₁ I.⇒ A₁ , I.K , K₀ {A₁}{B₁}) → A₀ ≡ A₁ 
K₀-inj₀ e =  I.inj⇒₁ (cong fst e) 
K₀-inj₁ : ∀{A₀ A₁ B₀ B₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ A₀ , I.K , K₀ {A₀}{B₀}) (A₁ I.⇒ B₁ I.⇒ A₁ , I.K , K₀ {A₁}{B₁}) → B₀ ≡ B₁ 
K₀-inj₁ e = I.inj⇒₁ (I.inj⇒₂ (cong fst e))

K₁-cong : ∀{A₀ A₁ B₀ B₁}{t₀ : I.Tm A₀}{t₁ : I.Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  B₀ ≡ B₁ → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (B₀ I.⇒ A₀ , I.K I.· t₀ , K₁ v₀) (B₁ I.⇒ A₁ , I.K I.· t₁ , K₁ v₁)  
K₁-cong {A₀ = A₀} {A₁ = A₁} b e = λ i → ((b i) I.⇒ (fst (e i))) , ((I.K I.· fst (snd (e i))) , K₁ (snd (snd (e i)))) 

K₁-inj₀ : ∀{A₀ A₁ B₀ B₁}{t₀ : I.Tm A₀}{t₁ : I.Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (B₀ I.⇒ A₀ , I.K I.· t₀ , K₁ v₀) (B₁ I.⇒ A₁ , I.K I.· t₁ , K₁ v₁) →
  A₀ ≡ A₁
K₁-inj₀ e = I.inj⇒₂ (cong fst e)
K₁-inj₁ : ∀{A₀ A₁ B₀ B₁}{t₀ : I.Tm A₀}{t₁ : I.Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (B₀ I.⇒ A₀ , I.K I.· t₀ , K₁ v₀) (B₁ I.⇒ A₁ , I.K I.· t₁ , K₁ v₁) →
  B₀ ≡ B₁
K₁-inj₁ e = I.inj⇒₁ (cong fst e)

K₁-inj₂ᵢ : ∀{A₀ A₁ B₀ B₁}{t₀ : I.Tm A₀}{t₁ : I.Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} → --A₀ ≡ A₁ → B₀ ≡ B₁ →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (B₀ I.⇒ A₀ , I.K I.· t₀ , K₁ v₀) (B₁ I.⇒ A₁ , I.K I.· t₁ , K₁ v₁) →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁)
K₁-inj₂ᵢ _Ind≡_.refl = _Ind≡_.refl
K₁-inj₂ : ∀{A₀ A₁ B₀ B₁}{t₀ : I.Tm A₀}{t₁ : I.Tm A₁}{v₀ : Nf A₀ t₀}{v₁ : Nf A₁ t₁} → --A₀ ≡ A₁ → B₀ ≡ B₁ →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (B₀ I.⇒ A₀ , I.K I.· t₀ , K₁ v₀) (B₁ I.⇒ A₁ , I.K I.· t₁ , K₁ v₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁)
K₁-inj₂ {A₀} {A₁} {B₀} {B₁} {t₀} {t₁} e = eqToPath (K₁-inj₂ᵢ (pathToEq e))


S₀-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → A₀ ≡ A₁ → B₀ ≡ B₁ → C₀ ≡ C₁ → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀)
S₀-cong a b c = λ i → (((a i) I.⇒ (b i) I.⇒ (c i)) I.⇒ ((a i) I.⇒ (b i)) I.⇒ (a i) I.⇒ (c i)) , (I.S , S₀)
S₀-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀) →
  A₀ ≡ A₁
S₀-inj₀ e = I.inj⇒₁ (I.inj⇒₁ (cong fst e))
S₀-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀) →
  B₀ ≡ B₁
S₀-inj₁ e = I.inj⇒₁ (I.inj⇒₂ (I.inj⇒₁ (cong fst e)))
S₀-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀ I.⇒ C₀) I.⇒ (A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S , S₀) ((A₁ I.⇒ B₁ I.⇒ C₁) I.⇒ (A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S , S₀) →
  C₀ ≡ C₁
S₀-inj₂ e = I.inj⇒₂ (I.inj⇒₂ (I.inj⇒₁ (cong fst e)))

S₁-congᵢ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁) →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁)
S₁-congᵢ _Ind≡_.refl = _Ind≡_.refl
S₁-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁)
S₁-cong e = eqToPath (S₁-congᵢ (pathToEq e))
S₁-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁) →
  A₀ ≡ A₁
S₁-inj₀ e = I.inj⇒₁ (I.inj⇒₁ (cong fst e))
S₁-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁) →
  B₀ ≡ B₁
S₁-inj₁ e = I.inj⇒₂ (I.inj⇒₁ (cong fst e))
S₁-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁) →
  C₀ ≡ C₁
S₁-inj₂ e = I.inj⇒₂ (I.inj⇒₂ (cong fst e))

S₁-inj₃ᵢ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁) →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁)
S₁-inj₃ᵢ _Ind≡_.refl = _Ind≡_.refl
S₁-inj₃ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁} → 
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} ((A₀ I.⇒ B₀) I.⇒ A₀ I.⇒ C₀ , I.S I.· t₀ , S₁ v₀) ((A₁ I.⇒ B₁) I.⇒ A₁ I.⇒ C₁ , I.S I.· t₁ , S₁ v₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁)
S₁-inj₃ e = eqToPath (S₁-inj₃ᵢ (pathToEq e))

fst≡Σ : ∀{T₁ T₂ : Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} → T₁ Ind≡ T₂ → fst T₁ Ind≡ fst T₂
fst≡Σ _Ind≡_.refl = _Ind≡_.refl

from :  ∀{A₀ A₁ B₀ B₁ C₀ C₁ : I.Ty} → (A₀ I.⇒ B₀ I.⇒ C₀) Ind≡ (A₁ I.⇒ B₁ I.⇒ C₁) → A₀ I.⇒ B₀ Ind≡ A₁ I.⇒ B₁
from indrefl = indrefl
indcong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x Ind≡ y → f x Ind≡ f y
indcong f indrefl = indrefl

S₂-congᵢ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  (ee : _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁)) →
  _Ind≡_ {A = Σ (I.Tm (A₁ I.⇒ B₁)) (Nf (A₁ I.⇒ B₁))} (indtransport (λ t → Σ (I.Tm t) (Nf t)) (from (indcong fst ee)) (u₀ , w₀)) (u₁ , w₁) → --(transport (Σ (I.Tm (_ => _)) (from (cong fst ee)) (Nf A)) (u₀ , w₀))
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁)
S₂-congᵢ indrefl indrefl = indrefl
S₂-cong : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ , u₀ , w₀) (A₁ I.⇒ B₁ , u₁ , w₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁)
S₂-cong {u₀ = u₀}{u₁ = u₁}{w₀ = w₀}{w₁ = w₁} e₁ e₂ = eqToPath (S₂-congᵢ (pathToEq e₁) (
  subst {x = pathToEq (cong fst e₂)}{y = from (indcong (λ r → pr₁ r) (pathToEq e₁))}
  (λ z → indtransport (λ t → Σ (I.Tm t) (Nf t)) z (u₀ , w₀) Ind≡ (u₁ , w₁))
  (sym (pathToEq-eqToPath (pathToEq (λ i → pr₁ (e₂ i)))) ∙ cong pathToEq (I.isTySet _ _ (eqToPath (pathToEq (λ i → pr₁ (e₂ i)))) (eqToPath (from (indcong (λ r → pr₁ r) (pathToEq e₁))))) ∙ pathToEq-eqToPath (from (indcong (λ r → pr₁ r) (pathToEq e₁))))
  (PathP→pathOver (λ t → Σ (I.Tm t) (Nf t)) (cong fst e₂) (cong snd e₂))))
S₂-inj₀ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  A₀ ≡ A₁
S₂-inj₀ e = (I.inj⇒₁ (cong fst e))

S₂-inj₁ᵢ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  B₀ Ind≡ B₁
S₂-inj₁ᵢ _Ind≡_.refl = _Ind≡_.refl
S₂-inj₁ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  B₀ ≡ B₁
S₂-inj₁ e = eqToPath (S₂-inj₁ᵢ (pathToEq e)) 
S₂-inj₂ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  C₀ ≡ C₁
S₂-inj₂ e = I.inj⇒₂ (cong fst e)

S₂-inj₃ᵢ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁)
S₂-inj₃ᵢ _Ind≡_.refl = _Ind≡_.refl
S₂-inj₃ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ I.⇒ C₀ , t₀ , v₀) (A₁ I.⇒ B₁ I.⇒ C₁ , t₁ , v₁)
S₂-inj₃ e = eqToPath (S₂-inj₃ᵢ (pathToEq e))

S₂-inj₄ᵢ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  _Ind≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ , u₀ , w₀) (A₁ I.⇒ B₁ , u₁ , w₁)
S₂-inj₄ᵢ _Ind≡_.refl = _Ind≡_.refl
S₂-inj₄ : ∀{A₀ A₁ B₀ B₁ C₀ C₁}{t₀ : I.Tm (A₀ I.⇒ B₀ I.⇒ C₀)}{t₁ : I.Tm (A₁ I.⇒ B₁ I.⇒ C₁)}{v₀ : Nf (A₀ I.⇒ B₀ I.⇒ C₀) t₀}{v₁ : Nf (A₁ I.⇒ B₁ I.⇒ C₁) t₁}{u₀ : I.Tm (A₀ I.⇒ B₀)}{u₁ : I.Tm (A₁ I.⇒ B₁)}{w₀ : Nf (A₀ I.⇒ B₀) u₀}{w₁ : Nf (A₁ I.⇒ B₁) u₁} →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ C₀ , I.S I.· t₀ I.· u₀ , S₂ v₀ w₀) (A₁ I.⇒ C₁ , I.S I.· t₁ I.· u₁ , S₂ v₁ w₁) →
  _≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ I.⇒ B₀ , u₀ , w₀) (A₁ I.⇒ B₁ , u₁ , w₁)
S₂-inj₄ e = eqToPath (S₂-inj₄ᵢ (pathToEq e))


infix 4 _≟_ 

_≟_ : ∀{A₀ A₁ t₀ t₁}(v₀ : Nf A₀ t₀)(v₁ : Nf A₁ t₁) → Dec (_≡_ {A = Σ I.Ty λ A → Σ (I.Tm A) (Nf A)} (A₀ , t₀ , v₀) (A₁ , t₁ , v₁))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} with I.discreteTy A₀ A₁ 
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | yes eA with I.discreteTy B₀ B₁ 
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | yes eA | yes eB = yes (K₀-cong eA eB)
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | yes eA | no ne = no (λ e → ne (K₀-inj₁  e))
K₀ {A₀}{B₀} ≟ K₀ {A₁}{B₁} | no ne = no λ e → ne (K₀-inj₀ e)
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ with I.discreteTy A₀ A₁ 
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | yes eA with I.discreteTy B₀ B₁  
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | yes eA | yes eB with v₀ ≟ v₁ 
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | yes eA | yes eB | yes eV = yes (K₁-cong eB eV)
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | yes eA | yes eB | no ne = no (λ e → ne (K₁-inj₂ e))
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁ | yes eA | no ne = no (λ e → ne (K₁-inj₁ e))
K₁ {A₀}{B₀} v₀ ≟ K₁ {A₁}{B₁} v₁  | no ne = no (λ e → ne (K₁-inj₀ e))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} with I.discreteTy A₀ A₁ 
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | yes eA with I.discreteTy B₀ B₁
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | yes eA | yes eB with I.discreteTy C₀ C₁
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | yes eA | yes eB | yes eC = yes (S₀-cong eA eB eC)
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | yes eA | yes eB | no ne = no (λ e → ne (S₀-inj₂ e))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | yes eA | no ne = no (λ e → ne (S₀-inj₁ e))
S₀ {A₀}{B₀}{C₀} ≟ S₀ {A₁}{B₁}{C₁} | no ne = no (λ e → ne (S₀-inj₀ e))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ with I.discreteTy A₀ A₁ 
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA with I.discreteTy B₀ B₁
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA | yes eB with I.discreteTy C₀ C₁
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA | yes eB | yes eC with v₀ ≟ v₁ 
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA | yes eB | yes eC | yes eV = yes (S₁-cong eV)
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA | yes eB | yes eC | no ne = no (λ e → ne (S₁-inj₃ e))
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA | yes eB | no ne = no λ e → ne (S₁-inj₂ e)
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | yes eA | no ne = no λ e → ne (S₁-inj₁ e)
S₁ {A₀}{B₀}{C₀} v₀ ≟ S₁ {A₁}{B₁}{C₁} v₁ | no ne = no λ e → ne (S₁-inj₀ e)
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ with I.discreteTy A₀ A₁ 
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA with I.discreteTy B₀ B₁
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB with I.discreteTy C₀ C₁
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB | yes eC with v₀ ≟ v₁ 
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB | yes eC | yes eV with w₀ ≟ w₁ 
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB | yes eC | yes eV | yes eW = yes (S₂-cong eV eW)
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB | yes eC | yes eV | no ne = no λ e → ne (S₂-inj₄ e)
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB | yes eC | no ne = no (λ e → ne (S₂-inj₃ e))
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | yes eB | no ne = no λ e → ne (S₂-inj₂ e)
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | yes eA | no ne = no λ e → ne (S₂-inj₁ e)
S₂ {A₀}{B₀}{C₀} v₀ w₀ ≟ S₂ {A₁}{B₁}{C₁} v₁ w₁ | no ne = no λ e → ne (S₂-inj₀ e)
K₀ ≟ K₁ _ = no λ e → transport (cong hDisjK₀ e) tt
K₀ ≟ S₀ = no λ e → transport (cong hDisjK₀ e) tt
K₀ ≟ S₁ v₁ = no λ e → transport (cong hDisjK₀ e) tt
K₀ ≟ S₂ v₁ v₂ = no λ e → transport (cong hDisjK₀ e) tt
K₁ v₀ ≟ K₀ = no λ e → transport (cong hDisjK₁ e) tt
K₁ v₀ ≟ S₀ = no λ e → transport (cong hDisjK₁ e) tt
K₁ v₀ ≟ S₁ v₁ = no λ e → transport (cong hDisjK₁ e) tt
K₁ v₀ ≟ S₂ v₁ v₂ = no λ e → transport (cong hDisjK₁ e) tt 
S₀ ≟ K₀ = no λ e → transport (cong hDisjS₀ e) tt
S₀ ≟ K₁ v₁ = no λ e → transport (cong hDisjS₀ e) tt
S₀ ≟ S₁ v₁ = no λ e → transport (cong hDisjS₀ e) tt
S₀ ≟ S₂ v₁ v₂ = no λ e → transport (cong hDisjS₀ e) tt
S₁ v₀ ≟ K₀ = no λ e → transport (cong hDisjS₁ e) tt
S₁ v₀ ≟ K₁ v₁ = no λ e → transport (cong hDisjS₁ e) tt
S₁ v₀ ≟ S₀ = no λ e → transport (cong hDisjS₁ e) tt
S₁ v₀ ≟ S₂ v₁ v₂ = no λ e → transport (cong hDisjS₁ e) tt
S₂ v₀ v₂ ≟ K₀ = no λ e → transport (cong hDisjS₂ e) tt
S₂ v₀ v₂ ≟ K₁ v₁ = no λ e → transport (cong hDisjS₂ e) tt
S₂ v₀ v₂ ≟ S₀ = no λ e → transport (cong hDisjS₂ e) tt
S₂ v₀ v₂ ≟ S₁ v₁ = no λ e → transport (cong hDisjS₂ e) tt

transport-ap : ∀{ℓ}{ℓ'}{A : Type ℓ'}{B : Type ℓ'}(P : B → Type ℓ)(f : A → B){x y : A}(e : x Ind≡ y){u : P (f x)} → indtransport (P ∘ f) e u Ind≡ indtransport P (ap f e) u
transport-ap P f indrefl = indrefl

TyTmIsSet : isSet (Σ I.Ty I.Tm)
TyTmIsSet = isSetΣ I.isTySet λ _ → I.TmSet

NfDiscrete : ∀{A t} → Discrete (Nf A t)
NfDiscrete {A}{t} n n' with n ≟ n'
NfDiscrete {A}{t} n n' | yes p with pathToEq p
NfDiscrete {A}{t} n n' | yes p | e = yes (eqToPath ((ap (λ z → indtransport (λ z → Nf (pr₁ z) (snd z)) z n) (pathToEq (sym (pathToEq-eqToPath indrefl) ∙ cong pathToEq (TyTmIsSet _ _ _ _) ∙ pathToEq-eqToPath (ap (λ z → pr₁ z , pr₁ (snd z)) e) )) Ind∙ Indsym (transport-ap (λ z → Nf (fst z) (snd z)) (λ z → (fst z , fst (snd z))) e)) Ind∙ apd (snd ∘ snd) e))
NfDiscrete {A}{t} n n' | no ¬p = no λ e → ¬p (cong (λ z → (A , t , z)) e)

NfSet : ∀{A t} → isSet (Nf A t)
NfSet {A}{t} = Discrete→isSet NfDiscrete
