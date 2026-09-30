{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module StricterSyntax.Syntax where

open import Lib
open import Syntax
open import Model
open import DepModel

open import StricterSyntax.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import StricterSyntax.D

module D = DepModel.DepModel D
module M = DepModel.DM D

Iₛ : Model {lzero} {lzero} {lzero}
Iₛ = record
      { sorts = record { Con = I.Con ; Sub = I.Sub ; Ty = I.Ty ; Tm = I.Tm }
      ; cwf = record
               { _∘_ = λ {Δ} {Γ} {Θ} γ δ →  L.fst (∣ M.⟦ γ ⟧Sub ∣ δ)
               ; ass = λ {Δ} {Γ} {γ} {Θ} {δ} {Ξ} {θ} →
                       let
                         (γ∘δ ,-) = ∣ M.⟦ γ ⟧Sub ∣ δ
                         ([γ∘δ]∘θ ,-) = ∣ M.⟦ γ∘δ ⟧Sub ∣ θ
                         (δ∘θ ,-) = ∣ M.⟦ δ ⟧Sub ∣ θ
                         (γ∘[δ∘θ] ,-) = ∣ M.⟦ γ ⟧Sub ∣ δ∘θ
                       in sym un ∙ cong I.∘ₑ $ refl $ refl $ refl $ sym un $ refl ∙ I.ass ∙ cong I.∘ₑ $ refl $ refl $ refl $ refl $ un ∙ un
               ; id = I.id
               ; idl = refl
               ; idr = λ {Δ} {Γ} {γ} →
                       let
                         (γ∘id ,-) = ∣ M.⟦ γ ⟧Sub ∣ I.id
                       in sym un ∙ I.idr
               ; ◇ = I.◇
               ; ε = I.ε
               ; ◇η = I.◇η
               ; _[_]T = λ {Γ} {n} {Δ} A γ → L.fst (∣ M.⟦ A ⟧Ty ∣ γ)
               ; [∘]T = λ {Γ} {n} {A} {Δ} {γ} {Θ} {δ} →
                        let
                          (γ∘δ ,-) = ∣ M.⟦ γ ⟧Sub ∣ δ
                          (A[γ∘δ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ∘δ
                          (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                          (A[γ][δ]T ,-) = ∣ M.⟦ A[γ]T ⟧Ty ∣ δ
                        in sym un ∙ cong (A I.[_]T) $ sym un ∙ I.[∘]T ∙ cong (I._[ δ ]T) $ un ∙ un
               ; [id]T = λ {Γ} {n} {A} →
                         let
                           (A[id]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.id
                         in sym un ∙ I.[id]T
               ; _[_]t = λ {Γ} {n} {A} {Δ} a γ → L.fst (∣ M.⟦ a ⟧Tm ∣ γ)
               ; [∘]t = {!!}
               ; [id]t = {!!}
               ; _▹_ = I._▹_
               ; p = I.p
               ; q = {!I.q!}
               ; _⁺ = {!!}
               ; ∘⁺ = {!!}
               ; id⁺ = {!!}
               ; ⟨_⟩ = I.⟨_⟩
               ; ⟨⟩∘ = {!!}
               ; p∘⁺ = {!!}
               ; p∘⟨⟩ = {!!}
               ; q[⁺] = {!!}
               ; q[⟨⟩] = {!!}
               ; ▹η = {!!}
               }
      ; liftT = record
                 { Lift = I.Lift
                 ; lift = I.lift
                 ; unlift = I.unlift
                 ; Liftβ = {!!}
                 ; Liftη = {!!}
                 ; Lift[] = refl
                 ; lift[] = refl
                 }
      ; u = record
             { U = I.U
             ; El = I.El
             ; cd = I.cd
             ; Uβ = {!!}
             ; Uη = {!!}
             ; U[] = refl
             ; cd[] = refl
             }
      ; pi = record
              { Π = I.Π
              ; Π[] = refl
              ; lam = I.lam
              ; app = λ {Γ} {n} {A} {B} f a → -- Sadness here! :(
                      let
                        (_ ,-) = ∣ M.⟦ B ⟧Ty ∣ I.⟨ a ⟩
                      in coe (cong (I.Tm Γ) $ un) (I.app f a)
              ; Πβ = {!!}
              ; Πη = {!!}
              ; lam[] = refl
              }
      ; bool = {!!}
      }

module Iₛ = Model.Model Iₛ

app[]ₛ : ∀{Γ Δ n}{A : Iₛ.Ty Γ n}{B : Iₛ.Ty (Γ Iₛ.▹ A) n}{f : Iₛ.Tm Γ (Iₛ.Π A B)}{a : Iₛ.Tm Γ A}{γ : Iₛ.Sub Δ Γ}
      → let
        (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
        (B[a]T ,-) = ∣ M.⟦ B ⟧Ty ∣ I.⟨ a ⟩
        (B[a][γ]T ,-) = ∣ M.⟦ B[a]T ⟧Ty ∣ γ
        (B[γ⁺]T ,-) = ∣ M.⟦ B ⟧Ty ∣ (γ Iₛ.⁺)
        (a[γ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ
        (B[γ⁺][a[γ]]T ,-) = ∣ M.⟦ B[γ⁺]T ⟧Ty ∣ I.⟨ a[γ]t ⟩
      in Iₛ.app f a Iₛ.[ γ ]t ≈ coe (sym (cong (Iₛ.Tm Δ) $ (sym un ∙ cong I._[ γ ]T $ sym un ∙ I.weave I.⟨⟩∘ ∙ cong I.[]Tₑ $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ refl $ (cong I.[]Tₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh ∙ un) $ (cong I.⟨⟩ₑ $ refl $ refl $ un $ un) ∙ un))) (Iₛ.app (f Iₛ.[ γ ]t) (a Iₛ.[ γ ]t))
app[]ₛ {A} {B} {f} {a} {γ} =
  let
    (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
    (B[γ⁺]T ,-) = ∣ M.⟦ B ⟧Ty ∣ (γ Iₛ.⁺)
    (f[γ]t ,-) = ∣ M.⟦ f ⟧Tm ∣ γ
    (a[γ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ
  in {!!} ∙ coh ∙ coh
{-
D-ből és I-ből összerakni egy Iₛ-t (strict syntax, ahol az Iₛ-be az I-ből válogatjuk össze a dolgokat,
kivéve a helyettesítési szabályt, amit a D-ből szedünk össze.)
-}
