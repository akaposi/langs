{-# OPTIONS --cubical #-}
{-# OPTIONS --allow-unsolved-metas #-} 
open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (_,_; Sub)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma hiding (Sub)
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (rec to exfalso)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Data.Equality renaming (funExt to IndfunExt; _≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ; ap to Indap) hiding (isProp)
open import Cubical.Foundations.Path

-- open import Cubical.Data.Equality.Conversion 
module mltt-minimal.Lib where

data UU : Type
ElU : UU → Type

data UU where
  ΠU  : (a : UU)(b : ElU a → UU) → UU 
  ΣU  : (a : UU)(b : ElU a → UU) → UU
  ⊥U  : UU

ElU (ΠU a b) = (x : ElU a) → ElU (b x)
ElU (ΣU a b) = Σ (ElU a) λ x → ElU (b x)
ElU ⊥U = ⊥

module UUPath where 
  substDep : {A A' : UU} → A Ind≡ A' → (ElU A → UU) → (ElU A' → UU) 
  substDep indrefl B = B

  CoverUU : UU → UU → Type 
  decode : (A A' : UU) → CoverUU A A' → A Ind≡ A' 
  decode-ΠU : {A A' : UU}{B : ElU A → UU}{B' : ElU A' → UU} → (AA' : A Ind≡ A') →  (∀ (a : ElU A) → CoverUU (B a) (B' (indtransport ElU AA' a))) → ΠU A B Ind≡ ΠU A' B'
  decode-ΣU : {A A' : UU}{B : ElU A → UU}{B' : ElU A' → UU} → (AA' : A Ind≡ A') → (∀ (a : ElU A) → CoverUU (B a) (B' (indtransport ElU AA' a))) → ΣU A B Ind≡ ΣU A' B'
  
  CoverUU ⊥U ⊥U = Unit
  CoverUU (ΠU A B) (ΠU A' B') = Σ[ aa' ∈ CoverUU A A' ]  (∀ (a : ElU A) → CoverUU (B a) (B' (indtransport ElU (decode A A' aa') a))) 
  CoverUU (ΣU A B) (ΣU A' B') = Σ[ aa' ∈ CoverUU A A' ] (∀ (a : ElU A) → CoverUU (B a) (B' (indtransport ElU (decode A A' aa') a))) 
  {-# CATCHALL #-}
  CoverUU _ _ = ⊥

  decode (ΠU A b) (ΠU A' b') (AA , p) = decode-ΠU (decode A A' AA) p 
  decode (ΣU A b) (ΣU A' b') (AA , p)  = decode-ΣU (decode A A' AA) p
  decode ⊥U ⊥U tt = indrefl
  decode-ΠU indrefl BB' = Indap (ΠU _) (IndfunExt (λ a → decode _ _ (BB' a))) 
  decode-ΣU indrefl BB' = Indap (ΣU _) (IndfunExt (λ a → decode _ _ (BB' a)))

  reflCode : (A : UU) → CoverUU A A 
  decodeRefl : (A : UU) → decode A A (reflCode A) ≡ indrefl

  reflCode (ΠU A B) = (reflCode A) ,  filler i1 
   --λ a → transport (cong (λ x → CoverUU (B a) (B (indtransport ElU x a))) ((sym (decodeRefl A)))) (reflCode (B a))
    module reflCodeΠU where 
      --- 
      filler : (i : I) → (∀ (a : ElU A) → CoverUU (B a) (B (indtransport ElU (decodeRefl A (~ i)) a)) )
      filler i a = transport⁻-filler (λ i → CoverUU (B a) ((B (indtransport ElU (decodeRefl A i) a))))  (reflCode (B a))  i 
  reflCode (ΣU A B) = (reflCode A) , (λ a → transport (cong (λ x → CoverUU (B a) (B (indtransport ElU x a))) ((sym (decodeRefl A)))) (reflCode (B a)))
  reflCode ⊥U = tt

            -- (λ i → decode-Π₁ (decodeRefl Aᴺ i) (reflCode-Π.filler Aᴺ Bᴺ (~ i))) ∙  cong (E.ap (Π Aᴺ)) (decodeRefl Bᴺ)                                                                              
  decodeRefl (ΠU A B) = (λ i → decode-ΠU (decodeRefl A i) (reflCodeΠU.filler A B  (~ i))) ∙ λ i → {! decodeRefl A  !} --cong (Indap (ΠU A)) {!   !} --cong (Indap (ΠU A)) {!  !}
  decodeRefl (ΣU A B) = {!  isOfHLevelPathP' !}
  decodeRefl ⊥U = refl
  -- (ΠU A B) = {!   !} --(λ i → decode-ΠU (decodeRefl A i) (reflCodeΠU.filler A B  (~ i))) ∙ cong {! Indap (ΠU A ) !} {!   !} --  cong₂ {! . !} {!   !} {!   !} --λ i → eqToPath {!   !} i --(cong₂ decode-ΠU (decodeRefl A) {!   !} ) ∙ cong (Indap (ΠU A)) λ i → {! IndfunExt  ?  !} --(λ i → decode-ΠU (decodeRefl A i) (reflCodeΠU.filler A (λ a → B a) (~ i))) ∙ cong (Indap (ΠU A)) {! decodeRefl ?  !}
  -- decodeRefl (ΣU A b) = {!   !}                                                                                   
  -- decodeRefl ⊥U = refl
-- {y..1 : Level} {A = A₁ : Type y..1} {B.ℓ : Level}
--       {B = B₁ : A₁ → Type B.ℓ} {x y : A₁} (f : (a : A₁) → B₁ a)
--       (p : x ≡ y) →
--       PathP (λ i → B₁ (p i)) (f x) (f y)
  encodeUU : (A A' : UU) → A Ind≡ A' → CoverUU A A'
  encodeUU A A' indrefl = reflCode A

  decodeEncode :
    (A A' : UU) (AA' : A Ind≡ A') →
    decode A A' (encodeUU A A' AA') ≡ AA'
  decodeEncode A .A indrefl =  decodeRefl A 

  isPropCover : (A A' : UU) → isProp (CoverUU A A')
  isPropCover (ΠU A B) (ΠU A' B') = isPropΣ (isPropCover A A') (λ AA' → isPropΠ (λ a → isPropCover (B a) (B' (indtransport ElU (decode A A' AA') a))))
  isPropCover (ΣU A B) (ΣU A' B') = isPropΣ (isPropCover A A') (λ AA' → isPropΠ (λ a → isPropCover (B a) (B' (indtransport ElU (decode A A' AA') a))))
  isPropCover ⊥U ⊥U = isPropUnit

isSetUU : isSet UU
isSetUU A A' = 
  isPropRetract 
    (λ AA' → encodeUU A A' (pathToEq AA')) 
    (λ AA' → eqToPath (decode A A' AA')) 
    (λ AA' → cong eqToPath  (decodeEncode A A' (pathToEq AA')) ∙ eqToPath-pathToEq AA') 
    (isPropCover A A')
  where
  open UUPath

isSetElU : (u : UU) → isSet (ElU u)
isSetElU (ΠU u b) = isSetΠ (λ x → isSetElU (b x))
isSetElU (ΣU u b) = isSetΣ (isSetElU u) (λ x → isSetElU (b x))
isSetElU ⊥U = λ x y  → exfalso x
-- coe : ∀{ℓ}{A B : Set ℓ} → A Ind≡ B → A → B
-- coe indrefl a = a

-- _≡[_]≡_ : ∀{ℓ}{A B : Set ℓ} → A → A ≡ B → B → Set ℓ
-- x ≡[ α ]≡ y = PathP (λ i → α i) x y

-- ap : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
--     → f a₀ ≡ f a₁
-- ap f a₂ = λ i → f (a₂ i)


transp2r : ∀{ℓ}{A B : Type ℓ}{a : A}{b : B}(p : B ≡ A) → transport (sym p) a ≡ b → a ≡ transport p b
transp2r {A = A}{B}{a}{b} p = J (λ A p → (a : A) → transport (sym p) a ≡ b → a ≡ transport p b) (λ a e → sym (transportRefl a) ∙ e ∙ sym (transportRefl b)) p a
subst2r : ∀{ℓ ℓ'}{A : Type ℓ}(P : A → Type ℓ'){a a' : A}(e : a' ≡ a){x : P a}{y : P a'} → subst P (sym e) x ≡ y → x ≡ subst P e y
subst2r P {a}{a'} e = transp2r {A = P a}{B = P a'}(λ i → P (e i))

transport-filler'' : ∀ {ℓ} {A B : Type ℓ} (p : B ≡ A) {x : A}{y : A}(e : x ≡ y)
                   → PathP (λ i → p i) (transport (λ i → p (~ i)) x) y
transport-filler'' p e i = transp (λ j → p (i ∨ ~ j)) i (e i)

substsubst : ∀{ℓ ℓ'}{A : Type ℓ}(P : A → Type ℓ'){a a' a'' : A}(e : a ≡ a')(e' : a' ≡ a''){x : P a}{y : P a''} → subst P (e ∙ e') x ≡ y → subst P e' (subst P e x) ≡ y
substsubst P {a}{a'}{a''} e e' {x} w = sym (substComposite P e e' x) ∙ w
