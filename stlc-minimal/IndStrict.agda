{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (Sub;_,_)
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to exfalso)

open import Cubical.Foundations.Transport
open import Cubical.Data.Equality renaming (_≡_ to _Ind≡_; transport to indtransport; refl to indrefl; _∙_ to _Ind∙_; sym to Indsym; J to IndJ)


open import stlc-minimal.Model
open import stlc-minimal.DepModel 
open import stlc-minimal.InitialModel

module stlc-minimal.IndStrict {ℓ}{ℓ'}(S : DepModel InStrict {ℓ}{ℓ'}) where

import stlc-minimal.Syntax as I

module IStrict = Model InStrict

transport-filler'' : ∀ {ℓ} {A B : Type ℓ} (p : B ≡ A) {x : A}{y : A}(e : x ≡ y)
                   → PathP (λ i → p i) (transport (λ i → p (~ i)) x) y
transport-filler'' p e i = transp (λ j → p (i ∨ ~ j)) i (e i)

module S = DepModel S

-- private variable
--   Γ Δ : I.Con
--   A B : I.Ty

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
subst[]∙' {Γ∙ = Γ∙}{A∙ = A∙}{Δ∙ = Δ∙}{a∙ = a∙} e {γ = γ}{γ∙ = γ∙} = congS (λ z → subst (S.Tm∙ Γ∙ A∙) z a∙ S.[ γ∙ ]∙) (λ i → eqToPath-pathToEq e (~ i)) ∙  (subst[]∙ (pathToEq e)) ∙ cong (λ z → subst (S.Tm∙ Δ∙ A∙) z  (a∙ S.[ γ∙ ]∙)) λ i → cong (λ z → z I.[ γ ]*)(eqToPath-pathToEq e i)

subst,∙ : ∀{Γ Δ A }{Δ∙ : S.Con∙ Δ}{Γ∙ : S.Con∙ Γ}{A∙ : S.Ty∙ A}{f g : I.Tm Γ A}{a∙ : S.Tm∙ Γ∙ A∙ f}{h : I.Sub Γ Δ}{h∙ : S.Sub∙ Γ∙ Δ∙ h}(e : f ≡ g) → 
  (h∙ S.,∙  subst (S.Tm∙ Γ∙ A∙) e a∙) ≡ transport (λ i → S.Sub∙ Γ∙ (Δ∙ S.▸∙ A∙) (h I., e i)) (h∙ S.,∙ a∙) 
subst,∙ {Δ∙ = Δ∙}{Γ∙ = Γ∙}{A∙}{f}{g}{a∙}{h}{h∙} e = J
  (λ g e → (h∙ S.,∙  subst (S.Tm∙ Γ∙ A∙) e a∙) ≡ transport (λ i → S.Sub∙ Γ∙ (Δ∙ S.▸∙ A∙) (h I., e i)) (h∙ S.,∙ a∙))
  (cong (h∙ S.,∙_) (substRefl {B = S.Tm∙ Γ∙ A∙} a∙) ∙ sym (transportRefl (h∙ S.,∙ a∙)))
  e

subst-app∙ : ∀ {Γ A B}{f g : I.Tm Γ (A I.⇒ B)}{a b : I.Tm Γ A}{Γ∙ : S.Con∙ Γ}{A∙ : S.Ty∙ A}{B∙ : S.Ty∙ B}{f∙ : S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙) f}{a∙ : S.Tm∙ Γ∙ A∙ a}(e1 : f ≡ g)(e2 : a ≡ b)  →
 subst (S.Tm∙ Γ∙ B∙) (λ i → I.app (e1 i) (e2 i)) (S.app∙ f∙ a∙) ≡ S.app∙ (subst (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) e1 f∙) (subst (S.Tm∙ Γ∙ A∙) e2 a∙)
subst-app∙ {Γ} {A} {B} {f} {g} {a} {b} {Γ∙} {A∙} {B∙} {f∙} {a∙} e1 e2 = J2 (λ g e1 b e2 → subst (S.Tm∙ Γ∙ B∙) (λ i → I.app (e1 i) (e2 i)) (S.app∙ f∙ a∙) ≡ S.app∙ (subst (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) e1 f∙) (subst (S.Tm∙ Γ∙ A∙) e2 a∙))
  (substRefl {B = S.Tm∙ Γ∙ B∙} (S.app∙ f∙ a∙) ∙ cong (λ z → S.app∙ z a∙) (sym (substRefl {B = (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙))} f∙)) ∙ cong (S.app∙ (subst (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) refl f∙)) (sym (substRefl {B = (S.Tm∙ Γ∙ A∙)} a∙)))
  e1 e2

subst-lam∙ : ∀{Γ : I.Con}{A B : I.Ty}{a b : I.Tm (Γ I.▸ A) B}{Γ∙ : S.Con∙ Γ}{A∙ : S.Ty∙ A}{B∙ : S.Ty∙ B}{a∙ : S.Tm∙ (Γ∙ S.▸∙ A∙) B∙ a}(e : a ≡ b) 
  →  subst (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) (λ i → I.lam (e i)) (S.lam∙ a∙) ≡ S.lam∙ (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) B∙) e a∙)
subst-lam∙ {Γ} {A} {B} {a} {b} {Γ∙} {A∙} {B∙} {a∙} e = J (λ b e → subst (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) (λ i → I.lam (e i)) (S.lam∙ a∙) ≡ S.lam∙ (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) B∙) e a∙))
  (substRefl {B = (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙))} (S.lam∙ a∙) ∙ cong S.lam∙ (sym (substRefl {B = (S.Tm∙ (Γ∙ S.▸∙ A∙) B∙)} a∙)))
  e

D : DepModel In
D .Con∙    = S.Con∙
D .Sub∙    = S.Sub∙
D .SubSet∙ = S.SubSet∙
D ._∘∙_    = S._∘∙_
D .assoc∙  = S.assoc∙
D .id∙     = S.id∙
D .idr∙    = S.idr∙
D .idl∙    = S.idl∙
D .Ty∙     = S.Ty∙
D .Tm∙     = S.Tm∙
D .TmSet∙  = S.TmSet∙
D ._[_]∙ {aˢ = aˢ}{γˢ = γˢ} {Δ = Δ}{A = A} t γ = subst (S.Tm∙ Δ A) (I._[_]= aˢ γˢ) (S._[_]∙ t γ)
D .[]-∘∙ {Γ}{A}{aˢ}{Δ}{γˢ}{Θ}{δˢ}{Γ∙}{Δ∙}{Θ∙}{A∙} a γ δ =  
  let
    S = S.Tm∙ Θ∙ A∙
    e0 = (((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) ∙ (λ i → ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) (~ i)))
    e1 = subst S (λ i → (aˢ I.[ γˢ ]=) i I.[ δˢ ]*) in
  toPathP
    ( sym (substComposite S (aˢ I.[ γˢ I.∘ δˢ ]=) (I.[]-∘ aˢ γˢ δˢ) (a S.[ γ S.∘∙ δ ]∙)) ∙
      subst2r S ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ)
        (sym (substComposite S ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) (sym ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ)) _) ∙
        subst2r S (λ i → (aˢ I.[ γˢ ]=) i I.[ δˢ ]*)
        (sym (substComposite S (((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) ∙ (λ i → ((aˢ I.[ γˢ I.∘ δˢ ]=) ∙ I.[]-∘ aˢ γˢ δˢ) (~ i))) (sym (λ i → (aˢ I.[ γˢ ]=) i I.[ δˢ ]*)) _) ∙
        cong (λ z → subst S z (a S.[ γ S.∘∙ δ ]∙)) (I.TmSet _ _ _ _) ∙
        fromPathP (S.[]-∘∙  a γ δ)) ∙
        sym (subst[]∙' {Γ∙ =  Δ∙} {A∙ = A∙} {Δ∙ =  Θ∙} {a∙ = (a S.[ γ ]∙)} (aˢ I.[ γˢ ]=) {γ = δˢ} {γ∙ = δ})))
D .[]-id∙ {aˢ = aˢ}{Γ = Γ}{A = A} a = toPathP (sym (substComposite (S.Tm∙ Γ A) (aˢ I.[ I.id ]=) (I.[]-id aˢ) (a S.[ S.id∙ ]∙)) ∙ fromPathP (S.[]-id∙ {aˢ = aˢ}{Γ = Γ}{A = A} a))
D ._▸∙_    = S._▸∙_ 
D .p∙      = S.p∙
D .q∙      = S.q∙
D ._,∙_    = S._,∙_                         
D .,-∘∙ {Γ}{Δ}{γˢ}{A}{aˢ}{Θ}{δˢ}{Δ∙}{Γ∙}{Θ∙}{A∙} γ a δ = 
  let 
    S = S.Sub∙  Θ∙ (Δ∙ S.▸∙ A∙)
    e0 = subst (S.Tm∙ Θ∙ A∙) (aˢ I.[ δˢ ]=) (a S.[ δ ]∙) in 
  toPathP 
   (sym ( subst,∙ {a∙ = a S.[ δ ]∙}{h∙ = γ S.∘∙ δ} (aˢ I.[ δˢ ]=) 
   ∙ subst2r S  (I.,-∘ γˢ aˢ δˢ) 
      (sym (substComposite S (λ i → (γˢ I.∘ δˢ I., (aˢ I.[ δˢ ]=) i)) (sym (I.,-∘ γˢ aˢ δˢ))  (γ S.∘∙ δ S.,∙ a S.[ δ ]∙)) 
      ∙ cong (λ rew → subst (S.Sub∙ Θ∙ (Δ∙ S.▸∙ A∙)) rew (γ S.∘∙ δ S.,∙ a S.[ δ ]∙)) (I.SubSet _ _ _ _) 
      ∙ sym (fromPathP⁻ (S.,-∘∙ γ a δ )))))   
D .▸-β₁∙   = S.▸-β₁∙  
D .▸-β₂∙ {Γ}{Δ}{γˢ}{A}{aˢ}{Γ∙}{Δ∙}{A∙} γ a = substRefl {B = (S.Tm∙ Δ∙ A∙) } (S.q∙ S.[ γ S.,∙ a ]∙) ◁ S.▸-β₂∙ γ a
D .▸-η∙    = S.▸-η∙  
D .◆∙      = S.◆∙
D .ε∙      = S.ε∙
D .ε-∘∙    = S.ε-∘∙
D .◆-η∙    = S.◆-η∙
D ._⇒∙_    = S._⇒∙_
D .app∙    = S.app∙ 
D .app-[]∙ {Γ}{A}{B}{f}{a}{Δ}{γ}{Γ∙}{Δ∙}{A∙}{B∙} f∙ a∙ γ∙ = 
  let
    S = (S.Tm∙ Δ∙ B∙)
    -- e0 = ?
    e1 = (f I.[ γ ]=)
    e2 = (a I.[ γ ]=)
  in 
  toPathP 
    (sym
      (substComposite (S.Tm∙ Δ∙ B∙) (λ i → ((λ i₁ → I.app (f I.[ γ ]*) ((a I.[ γ ]=) i₁))  ∙ (λ i₁ → I.app ((f I.[ γ ]=) i₁) (a I.[ γ ])) ∙ (λ i₁ → I.app-[] f a γ (~ i₁))) i) (I.app-[] f a γ)  (S.app∙ f∙ a∙ S.[ γ∙ ]∙)) 
      ∙ sym (congS  (λ z → subst S  (λ i → I.app ((f I.[ γ ]=) i) ((a I.[ γ ]=) i)) z) (sym (S.app-[]∙ f∙ a∙ γ∙ )) ∙ congS (λ rew → subst S rew (S.app∙ f∙ a∙ S.[ γ∙ ]∙)) (I.TmSet _ _ _ _)) ∙ subst-app∙ {f∙ = f∙ S.[ γ∙ ]∙} {a∙ = a∙ S.[ γ∙ ]∙} e1 e2) 
D .lam∙    = S.lam∙  
D .lam-[]∙ {B}{Γ}{A}{b}{Δ}{γ}{Γ∙}{Δ∙}{A∙}{B∙} b∙ γ∙ = toPathP (sym (substComposite (S.Tm∙ Δ∙ (A∙ S.⇒∙ B∙)) ((λ i → I.lam ((b I.[ γ I.∘ I.p I., I.q ]=) i)) ∙  (λ i → I.lam-[] b γ (~ i))) (I.lam-[] b γ ) (S.lam∙ b∙ S.[ γ∙ ]∙)) ∙ sym (congS (λ z → subst (S.Tm∙ Δ∙ (A∙ S.⇒∙ B∙)) (λ i → I.lam ((b I.[ γ I.↑ ]=) i)) z) (sym (S.lam-[]∙ b∙ γ∙))  ∙ congS (λ rew → subst (S.Tm∙ Δ∙ (A∙ S.⇒∙ B∙)) rew (S.lam∙ b∙ S.[ γ∙ ]∙)) (I.TmSet _ _ _ _)) ∙ subst-lam∙ (I._[_]=  _ _))
D .⇒-β∙    {B}{Γ}{A}{bˢ}{aˢ}{Γ∙}{A∙}{B∙} b a = toPathP (subst2r (S.Tm∙ Γ∙ B∙) (bˢ I.[ I.id I., aˢ ]=) (sym (substComposite  (S.Tm∙ Γ∙ B∙)  (I.⇒-β bˢ aˢ)  (sym (bˢ I.[ I.id I., aˢ ]=)) (S.app∙ (S.lam∙ b) a)) ∙ fromPathP (S.⇒-β∙ b a)))
D .⇒-η∙    {Γ}{A}{B}{f}{Γ∙}{A∙}{B∙} f∙ =
  let
    S =  S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)
    p = S.⇒-η∙
    pr = fromPathP (p f∙)
    e0 = sym (I._[_]= f I.p )
    e1 = sym (congS (λ t → I.lam (I.app t I.q)) e0)
  in
  toPathP 
    (subst2r S (e1 ∙ I.⇒-η f) (sym ( substComposite S (I.⇒-η f) ((sym ((λ i → I.lam (I.app ((f I.[ I.p ]=) i) I.q)) ∙ I.⇒-η f))) (S.lam∙ (S.app∙ (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) (A∙ S.⇒∙ B∙)) (f I.[ I.p ]=)  (f∙ S.[ S.p∙ ]∙)) S.q∙)) ) 
    ∙ congS (λ rew → subst (S.Tm∙ Γ∙ (A∙ S.⇒∙ B∙)) rew (S.lam∙ (S.app∙ (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) (A∙ S.⇒∙ B∙)) (f I.[ I.p ]=) (f∙ S.[  S.p∙ ]∙))  S.q∙))) (I.TmSet _ _ _ _)
    ∙ subst-lam∙ {Γ∙ =  Γ∙}{A∙ = A∙}{ B∙ = B∙ }{a∙ = (S.app∙ (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) (A∙ S.⇒∙ B∙)) (f I.[ I.p ]=) (f∙ S.[ S.p∙ ]∙)) S.q∙)} (congS (λ t → I.app t I.q) e0) ∙ cong (λ z → S.lam∙ z) ((subst-app∙ {Γ∙ = Γ∙ S.▸∙ A∙}{B∙ = B∙} (sym (f I.[ I.p ]=)) λ i → I.q) 
        ∙ cong (λ z → S.app∙ z (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) A∙) (λ i → I.q) S.q∙)) (sym (substComposite (S.Tm∙ (Γ∙ S.▸∙ A∙) (A∙ S.⇒∙ B∙)) (f I.[ I.p ]=) (sym (f I.[ I.p ]=)) (f∙ S.[ S.p∙ ]∙))) 
        ∙ congS (λ z → S.app∙ z (subst (S.Tm∙ (Γ∙ S.▸∙ A∙) A∙) (λ i → I.q) S.q∙)) (congS (λ rew → subst (S.Tm∙ (Γ∙ S.▸∙ A∙) (A∙ S.⇒∙ B∙)) rew (f∙ S.[ S.p∙ ]∙)) (I.TmSet _ _ _ _) 
        ∙ substRefl {B =  (S.Tm∙ (Γ∙ S.▸∙ A∙) (A∙ S.⇒∙ B∙))} (f∙ S.[ S.p∙ ]∙)) 
        ∙ congS (λ z → S.app∙ (f∙ S.[ S.p∙ ]∙) z) (substRefl {B =(S.Tm∙ (Γ∙ S.▸∙ A∙) A∙)} S.q∙))) 
        ∙ pr)
D .ι∙      = S.ι∙                                                                                                                                                                                                                                                                                                                                

import stlc-minimal.Ind D as Ind

⟦_⟧T : (A : IStrict.Ty) → S.Ty∙ A
⟦_⟧T = Ind.⟦_⟧Tᵢ
⟦_⟧C : (Γ : IStrict.Con) → S.Con∙ Γ
⟦_⟧C = Ind.⟦_⟧Cᵢ
⟦_⟧S : ∀{Δ Γ}(γ : IStrict.Sub Δ Γ) → S.Sub∙ (⟦ Δ ⟧C) (⟦ Γ ⟧C) γ
⟦_⟧S = Ind.⟦_⟧Sᵢ
⟦_⟧t : ∀{Γ A}(a : IStrict.Tm Γ A) → S.Tm∙ (⟦ Γ ⟧C) (⟦ A ⟧T) a
⟦_⟧t = Ind.⟦_⟧tᵢ
