{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

--------- Bool stuff -------------------------------
module Dictatorship.QIIRT.Bool where

open import Lib
open import Dictatorship.Syntax
open import Dictatorship.DepModel
open I

open import Dictatorship.QIIRT.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import Dictatorship.QIIRT.CwF

Bool∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Ty∙ Γ∙ Bool
Bool∙ = Ty∙.constructor λ _ → Bool ,ₚ Bool[]

Bool[]∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ} → Bool∙ [ γ∙ ]T∙ ~[ cong (Ty∙ _) $ Bool[] ] Bool∙
Bool[]∙ {γ∙} = cong mkTy∙ $ Bool[] $ funext λ {Θ} → funext λ {δ} → Σ-extₚ refl (funext (cong (_≈ _) $ (cong _[ δ ]T $ Bool[])))

true∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ true
true∙ = Tm∙.constructor λ _ → true ,ₚ true[]

false∙ : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ false
false∙ = Tm∙.constructor λ _ → false ,ₚ false[]

true[]∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
        → true∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ true[] ] true∙
true[]∙ {γ∙} = cong mkTm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ true[] $ funext λ {Θ} → funext λ {δ} → Σ-extₚ refl (funext (cong ~ₑ $ (cong (Tm Θ) $ (cong _[ δ ]T $ Bool[])) $ (cong []tₑ $ refl $ refl $ Bool[] $ true[] $ refl) $ refl $ refl))

false[]∙ : ∀{Δ Γ}{Δ∙ : Con∙ Δ}{Γ∙ : Con∙ Γ}{γ}{γ∙ : Sub∙ Δ∙ Γ∙ γ}
         → false∙ [ γ∙ ]t∙ ~[ cong (Tm∙ₑ _) $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ false[] ] false∙
false[]∙ {γ∙} = cong mkTm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ false[] $ funext λ {Θ} → funext λ {δ} → Σ-extₚ refl (funext (cong ~ₑ $ (cong (Tm Θ) $ (cong _[ δ ]T $ Bool[])) $ (cong []tₑ $ refl $ refl $ Bool[] $ false[] $ refl) $ refl $ refl))
                                                                                                                                                                                                                                                       
elim∙    : {Γ : Con} {A : Ty (Γ ▹ Bool)}
           {a : Tm Γ (A [ ⟨ true ⟩ ]T)}
           {b : Tm Γ (A [ ⟨ false ⟩ ]T)}
           {c : Tm Γ Bool}
           {Γ∙ : Con∙ Γ}
           (A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) A)
           (a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a)
           (b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b)
           (c∙ : Tm∙ Γ∙ Bool∙ c)
         → Tm∙ Γ∙ (A∙ [ ⟨ c∙ ⟩∙ ]T∙) (elim A a b c)
elim∙ {A} {a} A∙ a∙ b∙ c∙ = Tm∙.constructor λ γ →
  let
    (c[γ]t ,-) = ∣ c∙ ∣ γ
    γ⁺ = coe (cong Sub $ (cong (_ ▹_) $ un) $ refl) (γ ⁺)
    (A[γ⁺]T ,-) = ∣ A∙ ∣ γ⁺
    (_ ,-) = ∣ A∙ ∣ (γ⁺ ∘ ⟨ c[γ]t ⟩)
    (_ ,-) = ∣ A∙ ∣ (γ⁺ ∘ ⟨ true ⟩)
    (_ ,-) = ∣ A∙ ∣ (γ⁺ ∘ ⟨ false ⟩)
    (a[γ]t ,-) = ∣ a∙ ∣ γ
    (b[γ]t ,-) = ∣ b∙ ∣ γ
  in coe (cong (Tm _) $ (cong _[ ⟨ c[γ]t ⟩ ]T $ sym un ∙ sym [∘]T ∙ un))
     (elim
       A[γ⁺]T
         (coe (cong (Tm _) $ (sym un ∙ [∘]T ∙ cong _[ ⟨ true ⟩ ]T $ un)) a[γ]t)
           (coe (cong (Tm _) $ (sym un ∙ [∘]T ∙ cong _[ ⟨ false ⟩ ]T $ un)) b[γ]t)
           c[γ]t)
  ,ₚ elim[] ∙ cong elim $ un $ (sym coh ∙ un ∙ coh) $ (sym coh ∙ un ∙ coh) $ (sym coh ∙ un) ∙ coh

elim[]∙  :
  {Γ Δ : Con}
  {A : Ty (Γ ▹ Bool)} →
  {a : Tm Γ (A [ ⟨ true ⟩ ]T)} {b : Tm Γ (A [ ⟨ false ⟩ ]T)} →
  {c : Tm Γ Bool} {γ : Sub Δ Γ}
  {Γ∙ : Con∙ Γ} {Δ∙ : Con∙ Δ}
  {A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) A} →
  {a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a} {b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b} →
  {c∙ : Tm∙ Γ∙ Bool∙ c} {γ∙ : Sub∙ Δ∙ Γ∙ γ} →
  let wt = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ true[])
      wf = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ false[])
      wc = ⟨⟩∘ ∙ cong (∘ₑ _) $ (cong (_ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ coh)
  in
  elim∙ A∙ a∙ b∙ c∙ [ γ∙ ]t∙
    ~[ cong (Tm∙ₑ _) $ weave wc $ refl $ weave∙ A∙ ⟨ c∙ ⟩∙ γ∙ (coe (cong Sub∙ₑ $ (cong (_ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (_ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙)) (⟨⟩∙ₑ Δ Δ∙ Bool Bool∙ (coe (cong (Tm Δ) $ Bool[]) (c [ γ ]t)) (coe (cong Tm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh) (c∙ [ γ∙ ]t∙))) wc (⟨⟩∘∙ {a∙ = c∙} {γ∙ = γ∙} ∙ cong (∘∙ₑ _ _) $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙}) $ refl $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ coh) $ coh $ (cong (⟨⟩∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙} $ coh $ coh)) $ elim[] ]
  elim∙
    (A∙ [ coe (cong Sub∙ₑ $ (cong (_ ▹_) $ Bool[]) $ refl $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙}) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙ ) ]T∙)
    (coe
      (cong (Tm∙ₑ _) $ weave wt $ refl $ weave∙ A∙ ⟨ true∙ ⟩∙ γ∙ (coe (cong Sub∙ₑ $ (cong (_ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (_ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙)) ⟨ true∙ ⟩∙ wt (⟨⟩∘∙ {a∙ = true∙} {γ∙ = γ∙} ∙ cong (∘∙ₑ _ _) $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙}) $ refl $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ true[]) $ coh $ (cong (⟨⟩∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙} $ true[] $ true[]∙ {γ∙ = γ∙})) $ coh)
      (a∙ [ γ∙ ]t∙))
    (coe
      (cong (Tm∙ₑ _) $ weave wf $ refl $ weave∙ A∙ ⟨ false∙ ⟩∙ γ∙ (coe (cong Sub∙ₑ $ (cong (_ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (_ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙) ) ⟨ false∙ ⟩∙ wf (⟨⟩∘∙ {a∙ = false∙} {γ∙ = γ∙} ∙ cong (∘∙ₑ _ _) $ (cong (_ ▹_) $ Bool[]) $ (cong (▹∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙}) $ refl $ refl $ coh $ (cong (⟨⟩ₑ _) $ Bool[] $ false[]) $ coh $ (cong (⟨⟩∙ₑ _ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙} $ false[] $ false[]∙ {γ∙ = γ∙})) $ coh)
      (b∙ [ γ∙ ]t∙))
    (coe
      (cong (Tm∙ₑ _) $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh)
      (c∙ [ γ∙ ]t∙))
elim[]∙ {Γ} {Δ} {A} {a} {b} {c} {γ} {Δ∙} {A∙} {a∙} {b∙} {c∙} {γ∙} = cong mkTm∙ₑ
  $ refl
  $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh))
  $ refl
  $ weave∙ A∙ ⟨ c∙ ⟩∙ γ∙
           (coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙))
           ⟨ coe (cong Tm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh) (c∙ [ γ∙ ]t∙) ⟩∙
           (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh))
           (⟨⟩∘∙ {a∙ = c∙} {γ∙ = γ∙} ∙ cong ∘∙ₑ $ refl $ refl $ (cong (Δ ▹_) $ Bool[]) $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh) $ coh $ (cong ⟨⟩∙ₑ $ refl $ refl $ Bool[] $ (cong mkTy∙ $ Bool[] $ funext (funext λ {δ} → Σ-extₚ refl (funext (cong (_≈ _) $ (cong _[ δ ]T $ Bool[]))))) $ coh $ coh))
  $ elim[]
  $ funext λ {Θ} → funext λ {δ} →
      let
        (γ∘δ ,-) = ∣ γ∙ ∣ δ
        (A[γ∘δ⁺]T ,-) = ∣ A∙ ∣ (coe (cong Sub $ (cong (Θ ▹_) $ Bool[]) $ refl) (γ∘δ ⁺))
        γ⁺ = coe (cong Sub $ (cong (Δ ▹_) $ Bool[]) $ refl) (γ ⁺)
        δ⁺ = coe (cong Sub $ (cong (Θ ▹_) $ Bool[]) $ refl) (δ ⁺)
        (a[γ∘δ]t ,-) = ∣ a∙ ∣ γ∘δ
        (b[γ∘δ]t ,-) = ∣ b∙ ∣ γ∘δ
        (c[γ∘δ]t ,-) = ∣ c∙ ∣ γ∘δ
        (γδ ,-) = ∣ coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong (▹∙ₑ Δ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙}) $ refl $ coh {e = cong Sub $ (cong (Δ ▹_) $ Bool[]) $ refl}) (_⁺∙ {A∙ = Bool∙} γ∙) ∣ δ⁺
        (a[γ][δ]t ,-) = ∣ coe
                          (cong (Tm∙ₑ Δ)
                            $ weave (⟨⟩∘ ∙ cong (∘ₑ (Γ ▹ Bool)) $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh {e = cong Sub $ (cong (Δ ▹_) $ Bool[]) $ refl} $ (cong (⟨⟩ₑ Δ) $ Bool[] $ true[]))
                            $ refl
                            $ weave∙ A∙ ⟨ true∙ ⟩∙ γ∙
                                (coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙))
                                ⟨ true∙ ⟩∙
                                (⟨⟩∘ ∙ cong (∘ₑ (Γ ▹ Bool)) $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ Δ) $ Bool[] $ true[]))
                                (⟨⟩∘∙ {a∙ = true∙} {γ∙ = γ∙}
                                ∙ cong (∘∙ₑ (Γ ▹ Bool) _)
                                    $ (cong (Δ ▹_) $ Bool[])
                                    $ (cong (▹∙ₑ Δ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙})
                                    $ refl
                                    $ refl
                                    $ coh
                                    $ (cong (⟨⟩ₑ Δ) $ Bool[] $ true[])
                                    $ coh
                                    $ (cong (⟨⟩∙ₑ Δ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙} $ true[] $ true[]∙ {γ∙ = γ∙}))
                            $ coh {e = cong (Tm Δ) $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ true[]))})
                          (a∙ [ γ∙ ]t∙) ∣ δ
        (b[γ][δ]t ,-) = ∣ coe
                          (cong (Tm∙ₑ Δ)
                            $ weave (⟨⟩∘ ∙ cong (∘ₑ (Γ ▹ Bool)) $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh {e = cong Sub $ (cong (Δ ▹_) $ Bool[]) $ refl} $ (cong (⟨⟩ₑ Δ) $ Bool[] $ false[]))
                            $ refl
                            $ weave∙ A∙ ⟨ false∙ ⟩∙ γ∙
                                (coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙))
                                ⟨ false∙ ⟩∙
                                (⟨⟩∘ ∙ cong (∘ₑ (Γ ▹ Bool)) $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong (⟨⟩ₑ Δ) $ Bool[] $ false[]))
                                (⟨⟩∘∙ {a∙ = false∙} {γ∙ = γ∙}
                                ∙ cong (∘∙ₑ (Γ ▹ Bool) _)
                                    $ (cong (Δ ▹_) $ Bool[])
                                    $ (cong (▹∙ₑ Δ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙})
                                    $ refl
                                    $ refl
                                    $ coh
                                    $ (cong (⟨⟩ₑ Δ) $ Bool[] $ false[])
                                    $ coh
                                    $ (cong (⟨⟩∙ₑ Δ _) $ Bool[] $ Bool[]∙ {γ∙ = γ∙} $ false[] $ false[]∙ {γ∙ = γ∙}))
                            $ coh {e = cong (Tm Δ) $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ false[]))})
                          (b∙ [ γ∙ ]t∙) ∣ δ
        (c[γ][δ]t ,-) = ∣ coe (cong (Tm∙ₑ Δ) $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh {e = cong (Tm Δ) $ Bool[]}) (c∙ [ γ∙ ]t∙) ∣ δ
      in Σ-extₚ (sym coh
                ∙ cong elim
                  $ (cong (λ x y → L.fst (∣ A∙ ∣ {x} y)) $ refl $ (sym coh ∙ cong _⁺ $ sym un ∙ ∘⁺ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ (cong (Θ ▹_) $ ((cong _[ δ ]T $ Bool[]) ∙ Bool[])) $ coh $ (cong ⁺ₑ $ refl $ refl $ Bool[] $ refl ∙ coh) ∙ un))
                    $ (sym coh ∙ sym un ∙ cong []tₑ $ refl $ refl $ refl $ refl $ sym un ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ true[])) $ coh $ refl ∙ un ∙ coh)
                    $ (sym coh ∙ sym un ∙ cong []tₑ $ refl $ refl $ refl $ refl $ sym un ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ false[])) $ coh $ refl ∙ un ∙ coh)
                    $ (sym un ∙ cong []tₑ $ refl $ refl $ refl $ refl $ sym un ∙ [∘]t ∙ cong []tₑ $ refl $ refl $ Bool[] $ coh $ refl ∙ un)
                ∙ coh)
                (funextₕ (cong (Tm Θ) $ (cong L.fstₑ $ refl $ (funext λ {z} → cong (λ x → Lift (x ≈ z)) $ (cong _[ δ ]T $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh)))) $
                  ({- this line is refl, remove it -} cong Ty∙∣∣ₑ $ reflₑ Δ $ refl $ reflₑ (A [ ⟨ c ⟩ ]T [ γ ]T) $ reflₑ (A∙ [ ⟨ c∙ ⟩∙ ]T∙ [ γ∙ ]T∙) $ reflₑ Θ $ reflₑ δ
                    ∙ cong Ty∙∣∣ₑ
                       $ reflₑ Δ
                       $ reflₑ Δ∙
                       $ weave (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh))
                       $[ A∙ [ ⟨ c∙ ⟩∙ ]T∙ [ γ∙ ]T∙ , A∙ [ coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙) ]T∙ [ ⟨ coe (cong Tm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh) (c∙ [ γ∙ ]t∙) ⟩∙ ]T∙ ]
                         weave∙ A∙ ⟨ c∙ ⟩∙ γ∙ (coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙)) ⟨ coe (cong Tm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh) (c∙ [ γ∙ ]t∙) ⟩∙
                           (⟨⟩∘ ∙ cong ∘ₑ $ refl $ (cong (Δ ▹_) $ Bool[]) $ refl $ coh $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh))
                           (⟨⟩∘∙ {a∙ = c∙} {γ∙ = γ∙} ∙ cong ∘∙ₑ $ refl $ refl $ (cong (Δ ▹_) $ Bool[])
                                                         $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[]))
                                                         $ refl
                                                         $ refl
                                                         $ coh
                                                         $ (cong ⟨⟩ₑ $ refl $ Bool[] $ coh)
                                                         $[ _⁺∙ {A∙ = Bool∙} γ∙ , coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙) ] coh
                                                         $[ ⟨ c∙ [ γ∙ ]t∙ ⟩∙ , ⟨ coe (cong Tm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh) (c∙ [ γ∙ ]t∙) ⟩∙ ] (cong ⟨⟩∙ₑ $ refl $ refl $ Bool[] $[ Bool∙ [ γ∙ ]T∙ , Bool∙ ] {!!} $ coh $[ {!!} , {!!} ] {!!}))
                       $ reflₑ Θ
                       $ reflₑ δ
                  ∙ {- this line is refl, remove it -} cong Ty∙∣∣ₑ $ reflₑ Δ $ refl $ refl $ reflₑ (A∙ [ coe (cong Sub∙ₑ $ (cong (Δ ▹_) $ Bool[]) $ refl $ (cong mkCon∙ $ (cong (Δ ▹_) $ Bool[])) $ refl $ coh) (_⁺∙ {A∙ = Bool∙} γ∙) ]T∙ [ ⟨ coe (cong Tm∙ₑ $ refl $ Bool[] $ refl $ Bool[]∙ {γ∙ = γ∙} $ coh) (c∙ [ γ∙ ]t∙) ⟩∙ ]T∙) $ reflₑ Θ $ reflₑ δ)))
                  λ e → {!!})
-- 
             -- cong L.fst $ (cong Ty∙∣∣ₑ $ reflₑ Δ $ refl $ reflₑ (A [ ⟨ c ⟩ ]T [ γ ]T) $ reflₑ (A∙ [ ⟨ c∙ ⟩∙ ]T∙ [ γ∙ ]T∙) $ reflₑ Θ $ reflₑ δ ∙ ?)
                                                                                                                                                   
Boolβ₁∙ : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) A}
          {a}{a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a}
            {b}{b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b}
        → elim∙ A∙ a∙ b∙ true∙ ~[ cong (Tm∙ _ _) $ Boolβ₁ ] a∙
Boolβ₁∙ = {!∘∙ₑ!}

Boolβ₂∙ : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ (Γ∙ ▹∙ Bool∙) A}
          {a}{a∙ : Tm∙ Γ∙ (A∙ [ ⟨ true∙ ⟩∙ ]T∙) a}
            {b}{b∙ : Tm∙ Γ∙ (A∙ [ ⟨ false∙ ⟩∙ ]T∙) b}
        → elim∙ A∙ a∙ b∙ false∙ ~[ cong (Tm∙ _ _) $ Boolβ₂ ] b∙
Boolβ₂∙ = {!!}
