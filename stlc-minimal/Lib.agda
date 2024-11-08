{-# OPTIONS --safe --cubical #-}

module stlc-minimal.Lib where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport


transp2r : ∀{ℓ}{A B : Type ℓ}{a : A}{b : B}(p : B ≡ A) → transport (sym p) a ≡ b → a ≡ transport p b
transp2r {A = A}{B}{a}{b} p = J (λ A p → (a : A) → transport (sym p) a ≡ b → a ≡ transport p b) (λ a e → sym (transportRefl a) ∙ e ∙ sym (transportRefl b)) p a
subst2r : ∀{ℓ ℓ'}{A : Type ℓ}(P : A → Type ℓ'){a a' : A}(e : a' ≡ a){x : P a}{y : P a'} → subst P (sym e) x ≡ y → x ≡ subst P e y
subst2r P {a}{a'} e = transp2r {A = P a}{B = P a'}(λ i → P (e i))

transport-filler'' : ∀ {ℓ} {A B : Type ℓ} (p : B ≡ A) {x : A}{y : A}(e : x ≡ y)
                   → PathP (λ i → p i) (transport (λ i → p (~ i)) x) y
transport-filler'' p e i = transp (λ j → p (i ∨ ~ j)) i (e i)

substsubst : ∀{ℓ ℓ'}{A : Type ℓ}(P : A → Type ℓ'){a a' a'' : A}(e : a ≡ a')(e' : a' ≡ a''){x : P a}{y : P a''} → subst P (e ∙ e') x ≡ y → subst P e' (subst P e x) ≡ y
substsubst P {a}{a'}{a''} e e' {x} w = sym (substComposite P e e' x) ∙ w
