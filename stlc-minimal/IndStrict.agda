{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)

open import Cubical.Foundations.Transport
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ)


open import stlc-minimal.DepModel 
open import stlc-minimal.InitialModel 

module stlc-minimal.IndStrict {ℓ}{ℓ'}(S : DepModel InStrict {ℓ}{ℓ'}) where

import stlc-minimal.Syntax as I

transport-filler'' : ∀ {ℓ} {A B : Type ℓ} (p : B ≡ A) {x : A}{y : A}(e : x ≡ y)
                   → PathP (λ i → p i) (transport (λ i → p (~ i)) x) y
transport-filler'' p e i = transp (λ j → p (i ∨ ~ j)) i (e i)

module S = DepModel S

open DepModel

transp2r : ∀{ℓ}{A B : Type ℓ}{a : A}{b : B}(p : B ≡ A) → transport (sym p) a ≡ b → a ≡ transport p b
transp2r {A = A}{B}{a}{b} p = J (λ A p → (a : A) → transport (sym p) a ≡ b → a ≡ transport p b) (λ a e → sym (transportRefl a) ∙ e ∙ sym (transportRefl b)) p a
subst2r : ∀{ℓ ℓ'}{A : Type ℓ}(P : A → Type ℓ'){a a' : A}(e : a' ≡ a){x : P a}{y : P a'} → subst P (sym e) x ≡ y → x ≡ subst P e y
subst2r P {a}{a'} e = transp2r {A = P a}{B = P a'}(λ i → P (e i))

subst[]∙ : ∀{Γ Δ A}{Γ∙ : S.Con∙ Γ}{A∙ : S.Ty∙ A}{Δ∙ : S.Con∙ Δ}{a b}{a∙ : S.Tm∙ Γ∙ A∙ a}(e : a Ind≡ b){γ : I.Sub Δ Γ}{γ∙ : S.Sub∙ Δ∙ Γ∙ γ} →
  subst (S.Tm∙ Γ∙ A∙) (eqToPath e) a∙ S.[ γ∙ ]∙ ≡ subst (S.Tm∙ Δ∙ A∙) (λ i →  (eqToPath e) i I.[ γ ]*) (a∙ S.[ γ∙ ]∙)
subst[]∙ {Γ∙ = Γ∙} {A∙ = A∙} {Δ∙ = Δ∙} {a = a} {a∙ = a∙} indrefl {γ = γ} {γ∙ = γ∙} = (cong (λ x → x S.[ γ∙ ]∙) (substRefl  {B = (S.Tm∙ Γ∙ A∙)} a∙)) ∙ sym (isSet-subst {B = (S.Tm∙ Δ∙ A∙)} I.TmSet (λ i → a I.[ γ ]*) (a∙ S.[ γ∙ ]∙) )

subst[]∙' : ∀{Γ Δ A}{Γ∙ : S.Con∙ Γ}{A∙ : S.Ty∙ A}{Δ∙ : S.Con∙ Δ}{a b}{a∙ : S.Tm∙ Γ∙ A∙ a}(e : a ≡ b){γ : I.Sub Δ Γ}{γ∙ : S.Sub∙ Δ∙ Γ∙ γ} →
  subst (S.Tm∙ Γ∙ A∙) e a∙ S.[ γ∙ ]∙ ≡ subst (S.Tm∙ Δ∙ A∙) (λ i → e i I.[ γ ]*) (a∙ S.[ γ∙ ]∙)
subst[]∙' e = {!   !}
-- transp (λ i → S.Tm∙ Γ∙ A∙ (e i)) i0 a∙ S.[ γ∙ ]∙ ≡
--       transp (λ i → S.Tm∙ Δ∙ A∙ (e i I.[ γ ]*)) i0 (a∙ S.[ γ∙ ]∙)
⟦_⟧ : DepModel InStrict → DepModel In
Con∙    ⟦ S ⟧ = S.Con∙
Sub∙    ⟦ S ⟧ = S.Sub∙
SubSet∙ ⟦ S ⟧ = S.SubSet∙
_∘∙_    ⟦ S ⟧ = S._∘∙_
assoc∙  ⟦ S ⟧ = S.assoc∙
id∙     ⟦ S ⟧ = S.id∙
idr∙    ⟦ S ⟧ = S.idr∙
idl∙    ⟦ S ⟧ = S.idl∙
Ty∙     ⟦ S ⟧ = S.Ty∙
Tm∙     ⟦ S ⟧ = S.Tm∙
TmSet∙  ⟦ S ⟧ = S.TmSet∙
_[_]∙   ⟦ S ⟧ {aˢ = aˢ}{γˢ = γˢ} {Δ = Δ}{A = A} t γ = subst (S.Tm∙ Δ A) (I._[_]= aˢ γˢ) (S._[_]∙ t γ)
[]-∘∙   ⟦ S ⟧ {Γ}{A}{aˢ}{Δ}{γˢ}{Θ}{δˢ}{Γ∙}{Δ∙}{Θ∙}{A∙} a γ δ = 
  let
    e0 = (((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) ∙ (λ i → ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) (~ i)))
    e1 = subst (S.Tm∙ Θ∙ A∙) (λ i → (aˢ I.[ γˢ ]=) i I.[ δˢ ]*) in
  toPathP (
  sym (substComposite (S.Tm∙ Θ∙ A∙) (aˢ I.[ γˢ I.∘ δˢ ]=) (I.[]-∘ aˢ γˢ δˢ) (a S.[ γ S.∘∙ δ ]∙)) ∙
  subst2r (S.Tm∙ Θ∙ A∙) ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ)
    (sym (substComposite (S.Tm∙ Θ∙ A∙) ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) (sym ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ)) _) ∙
    subst2r (S.Tm∙ Θ∙ A∙) (λ i → (aˢ I.[ γˢ ]=) i I.[ δˢ ]*)
    (sym (substComposite (S.Tm∙ Θ∙ A∙) (((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) ∙ (λ i → ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) (~ i))) (sym (λ i → (aˢ I.[ γˢ ]=) i I.[ δˢ ]*)) _) ∙
    cong (λ z → subst (S.Tm∙ Θ∙ A∙) z (a S.[ γ S.∘∙ δ ]∙)) (I.TmSet _ _ _ _) ∙
    fromPathP (S.[]-∘∙  a γ δ)) ∙
    sym (subst[]∙' {Γ∙ =  Δ∙} {A∙ = A∙} {Δ∙ =  Θ∙} {a∙ = (a S.[ γ ]∙)} (aˢ I.[ γˢ ]=) {γ = δˢ} {γ∙ = δ})))
[]-id∙  ⟦ S ⟧ {aˢ = aˢ}{Γ = Γ}{A = A} a = toPathP (sym (substComposite (S.Tm∙ Γ A) (aˢ I.[ I.id ]=) (I.[]-id aˢ) (a S.[ S.id∙ ]∙)) ∙ fromPathP (S.[]-id∙ {aˢ = aˢ}{Γ = Γ}{A = A} a))
_▸∙_    ⟦ S ⟧ = S._▸∙_ 
p∙      ⟦ S ⟧ = S.p∙
q∙      ⟦ S ⟧ = S.q∙
_,∙_    ⟦ S ⟧ = S._,∙_                          --toPathP {!  S.,-∘∙ γ a δ !} 
,-∘∙    ⟦ S ⟧ {Γ}{Δ}{γˢ}{A}{aˢ}{Θ}{δˢ}{Γ∙}{Δ∙}{Θ∙}{A∙} γ a δ = {!  S.,-∘∙ γ a δ !} -- toPathP {!  sym (substComposite (S.Sub∙ Θ∙ (Γ∙ S.▸∙ A∙)) (I.,-∘ γˢ aˢ δˢ) (λ i₁ → γˢ I.∘ δˢ I., (aˢ I.[ δˢ ]=) (~ i₁)) ?) !} --{!   ∙ ? !} -- toPathP {!  substComposite  (λ i → S.Sub∙ Θ (Γ S.▸∙ A) (I.,-∘ γˢ aˢ δˢ i))!} -- S.,-∘∙  γ a δ 
▸-β₁∙   ⟦ S ⟧ = S.▸-β₁∙  
▸-β₂∙   ⟦ S ⟧ {Γ}{Δ}{γˢ}{A}{aˢ}{Γ∙}{Δ∙}{A∙} γ a = substRefl {B = (S.Tm∙ Δ∙ A∙) } (S.q∙ S.[ γ S.,∙ a ]∙) ◁ S.▸-β₂∙ γ a
▸-η∙    ⟦ S ⟧ = S.▸-η∙  
◆∙      ⟦ S ⟧ = S.◆∙
ε∙      ⟦ S ⟧ = S.ε∙
ε-∘∙    ⟦ S ⟧ = S.ε-∘∙
◆-η∙    ⟦ S ⟧ = S.◆-η∙
_⇒∙_    ⟦ S ⟧ = S._⇒∙_
app∙    ⟦ S ⟧ = S.app∙
app-[]∙ ⟦ S ⟧ f a γ = {!  S.app-[]∙ f a γ  !}
lam∙    ⟦ S ⟧ = S.lam∙
lam-[]∙ ⟦ S ⟧ b γ = {! S.lam-[]∙ b γ   !}
⇒-β∙    ⟦ S ⟧ {A}{Γ}{B}{bˢ}{aˢ}{Γ∙}{B∙}{A∙} b a = toPathP {!  ?  ∙ (fromPathP (S.⇒-β∙ b a))!}
-- {!substComposite  (S.Tm∙ Γ∙ A∙) (I.⇒-β bˢ aˢ)  (λ i₁ → (bˢ I.[ I.id I., aˢ ]=) (~ i₁))  (S.app∙ (S.lam∙ b) a)!} 
-- toPathP {!  substComposite (S.Tm∙ Γ B) !}
⇒-η∙    ⟦ S ⟧ {Γ}{A}{B}{f}{Γ∙}{A∙}{B∙} f∙ = toPathP ({!sym (substComposite  (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) ? (I.⇒-η f ) (S.lam∙ (S.app∙ (f∙ S.[ S.p∙ ]∙) S.q∙)))!} ∙ (fromPathP (S.⇒-η∙ f∙)))  -- S.⇒-η∙ f 
ι∙      ⟦ S ⟧ = S.ι∙
  --  PathP
  --   (λ i →
  --      S.Tm∙ Γ B
  --      ((I.⇒-β bˢ aˢ ∙ (λ i₁ → (bˢ I.[ I.id I., aˢ ]=) (~ i₁))) i))
  --   (S.app∙ (S.lam∙ b) a) (b S.[ S.id∙ S.,∙ a ]∙)
