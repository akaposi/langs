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
               ; [∘]t = λ {Γ} {n} {A} {a} {Δ} {γ} {Θ} {δ} →
                        let
                          (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                          (γ∘δ ,-) = ∣ M.⟦ γ ⟧Sub ∣ δ
                          (a[γ∘δ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ∘δ
                          (a[γ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ
                          (a[γ][δ]t ,-) = ∣ M.⟦ a[γ]t ⟧Tm ∣ δ
                        in sym un ∙ cong I.[]tₑ $ refl $ refl $ refl $ refl $ refl $ sym un ∙ I.[∘]t ∙ cong I.[]tₑ $ refl $ refl $ refl $ un $ un $ refl ∙ un
               ; [id]t = λ {n} {Γ} {A} {a} →
                         let
                           (a[id]t ,-) = ∣ M.⟦ a ⟧Tm ∣ I.id
                         in sym un ∙ I.[id]t
               ; _▹_ = I._▹_
               ; p = I.p
               ; q = λ {Γ} {n} {A} →
                     let
                       (A[p]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.p
                     in coe (cong (I.Tm (Γ I.▹ A)) $ un) I.q
               ; _⁺ = λ {Δ} {Γ} {n} {A} γ →
                      let
                        (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                      in coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺)
               ; ∘⁺ = λ {Δ} {Γ} {γ} {Θ} {δ} {n} {A} →
                      let
                        (γ∘δ ,-) = ∣ M.⟦ γ ⟧Sub ∣ δ
                        (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                        (A[γ][δ]T ,-) = ∣ M.⟦ A[γ]T ⟧Ty ∣ δ
                        (γ⁺∘δ⁺ ,-) = ∣ coe (cong D.Sub∙ₑ
                                        $ M.Sub-inj₁ {Γ = Δ} (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl)
                                        $ M.Sub-inj₂ (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl)
                                        $ (cong M.⟦_⟧Con $ M.Sub-inj₁ {Γ = Δ} (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl))
                                        $ (cong M.⟦_⟧Con $ M.Sub-inj₂ (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl))
                                        $[ γ I.⁺ , coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺) ] coh) (D._⁺∙ {A∙ = M.⟦ A ⟧Ty} M.⟦ γ ⟧Sub) ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (δ I.⁺))
                      in sym coh ∙ cong I.⁺ₑ $ refl $ refl $ refl $ refl $ sym un ∙ I.∘⁺ ∙ cong I.∘ₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ (cong I.▹ₑ $ refl $ refl $ (cong I._[ δ ]T $ un ∙ un)) $ coh $ (cong I.⁺ₑ $ refl $ refl $ refl $ un $ refl ∙ coh) ∙ un
               ; id⁺ = λ {Γ} {n} {A} → sym coh ∙ I.id⁺
               ; ⟨_⟩ = I.⟨_⟩
               ; ⟨⟩∘ = λ {Γ} {n} {A} {a} {Δ} {γ} →
                       let
                         (⟨a⟩∘γ ,-) = ∣ D.⟨ M.⟦ a ⟧Tm ⟩∙ ∣ γ
                         (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                         (a[γ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ
                         (γ⁺∘⟨a[γ]t⟩ ,-) = ∣ coe (cong D.Sub∙ₑ
                                                $ M.Sub-inj₁ {Γ = Γ} (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl)
                                                $ M.Sub-inj₂ (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl)
                                                $ (cong M.⟦_⟧Con $ M.Sub-inj₁ {Γ = Γ} (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl))
                                                $ (cong M.⟦_⟧Con $ M.Sub-inj₂ (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl))
                                                $[ _ , coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺) ] coh) (D._⁺∙ {A∙ = M.⟦ A ⟧Ty} M.⟦ γ ⟧Sub) ∣ I.⟨ a[γ]t ⟩
                       in sym un ∙ I.⟨⟩∘ ∙ cong I.∘ₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh $ (cong I.⟨⟩ₑ $ refl $ refl $ un $ un) ∙ un
               ; p∘⁺ = λ {Γ} {n} {A} {Δ} {γ} →
                       let
                         (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                         (p∘γ⁺ ,-) = ∣ D.p∙ {A∙ = M.⟦ A ⟧Ty} ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺))
                         (γ∘p ,-) = ∣ M.⟦ γ ⟧Sub ∣ (I.p {A = A[γ]T})
                       in sym un ∙ cong I.∘ₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ refl $ sym coh ∙ I.p∘⁺ ∙ cong I.∘ₑ $ refl $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ (cong I.pₑ $ refl $ refl $ un) ∙ un
               ; p∘⟨⟩ = λ {Γ} {n} {A} {a} →
                        let
                          (p∘⟨a⟩ ,-) = ∣ D.p∙ {A∙ = M.⟦ A ⟧Ty} ∣ I.⟨ a ⟩
                        in sym un ∙ I.p∘⟨⟩
               ; q[⁺] = λ {Δ} {Γ} {γ} {n} {A} →
                        let
                          (A[p]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.p
                          (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
                          (A[γ][p]T ,-) = ∣ M.⟦ A[γ]T ⟧Ty ∣ (I.p {A = A[γ]T})
                          γ⁺ = coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺)
                          Dq = coe (cong D.Tm∙ₑ
                                      $ M.Tm-inj₁ (cong (I.Tm (Γ I.▹ A)) $ un)
                                      $ M.Tm-inj₂ (cong (I.Tm (Γ I.▹ A)) $ un)
                                      $ M.Tm-inj₃ (cong (I.Tm (Γ I.▹ A)) $ un)
                                      $ (cong M.⟦_⟧Con $ M.Tm-inj₁ (cong (I.Tm (Γ I.▹ A)) $ un))
                                      $ (cong M.⟦⟧Tyₑ
                                           $ M.Tm-inj₁ (cong (I.Tm (Γ I.▹ A)) $ un)
                                           $ M.Tm-inj₂ (cong (I.Tm (Γ I.▹ A)) $ un)
                                           $ M.Tm-inj₃ (cong (I.Tm (Γ I.▹ A)) $ un))
                                      $[ I.q , coe (cong (I.Tm (Γ I.▹ A)) $ un) I.q ] coh) (D.q∙ {A∙ = M.⟦ A ⟧Ty})
                          (q[γ⁺]t ,-) = ∣ Dq ∣ γ⁺
                        in sym un ∙ cong I.[]tₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ sym un) $ refl $ sym un $ sym coh $ sym coh ∙ I.q[⁺] ∙ cong I.qₑ $ refl $ refl $ un ∙ coh
               ; q[⟨⟩] = λ {Γ} {n} {A} {a} →
                         let
                           (A[p]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.p
                           Dq = coe (cong D.Tm∙ₑ
                                       $ M.Tm-inj₁ (cong (I.Tm (Γ I.▹ A)) $ un)
                                       $ M.Tm-inj₂ (cong (I.Tm (Γ I.▹ A)) $ un)
                                       $ M.Tm-inj₃ (cong (I.Tm (Γ I.▹ A)) $ un)
                                       $ (cong M.⟦_⟧Con $ M.Tm-inj₁ (cong (I.Tm (Γ I.▹ A)) $ un))
                                       $ (cong M.⟦⟧Tyₑ
                                            $ M.Tm-inj₁ (cong (I.Tm (Γ I.▹ A)) $ un)
                                            $ M.Tm-inj₂ (cong (I.Tm (Γ I.▹ A)) $ un)
                                            $ M.Tm-inj₃ (cong (I.Tm (Γ I.▹ A)) $ un))
                                       $[ I.q , coe (cong (I.Tm (Γ I.▹ A)) $ un) I.q ] coh) (D.q∙ {A∙ = M.⟦ A ⟧Ty})
                           (q⟨a⟩ ,-) = ∣ Dq ∣ I.⟨ a ⟩ 
                         in sym un ∙ cong I.[]tₑ $ refl $ refl $ refl $ sym un $ sym coh $ refl ∙ I.q[⟨⟩]
               ; ▹η = λ {Γ} {n} {A} →
                      let
                        (A[p]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.p
                        q' = coe (cong (I.Tm (Γ I.▹ A)) $ un) I.q
                        (p⁺∘q ,-) = ∣ coe (cong D.Sub∙ₑ
                                           $ M.Sub-inj₁ {Γ = Γ} (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl)
                                           $ M.Sub-inj₂ (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl)
                                           $ (cong M.⟦_⟧Con $ M.Sub-inj₁ {Γ = Γ} (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl))
                                           $ (cong M.⟦_⟧Con $ M.Sub-inj₂ (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl))
                                           $[ I.p I.⁺ , coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (I.p I.⁺) ] coh) (D._⁺∙ {A∙ = M.⟦ A ⟧Ty} (D.p∙ {A∙ = M.⟦ A ⟧Ty})) ∣ I.⟨ q' ⟩
                      in I.▹η ∙ cong I.∘ₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ un) $ refl $ coh $ (cong I.⟨⟩ₑ $ refl $ refl $ un $ coh) ∙ un
               }
      ; liftT = record
                 { Lift = I.Lift
                 ; lift = I.lift
                 ; unlift = I.unlift
                 ; Liftβ = I.Liftβ
                 ; Liftη = I.Liftη
                 ; Lift[] = refl
                 ; lift[] = refl
                 }
      ; u = record
             { U = I.U
             ; El = I.El
             ; cd = I.cd
             ; Uβ = I.Uβ
             ; Uη = I.Uη
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
              ; Πβ = λ {n} {Γ} {A} {B} {b} {a} →
                     let
                       (b⟨a⟩ ,-) = ∣ M.⟦ b ⟧Tm ∣ I.⟨ a ⟩                       
                     in sym coh ∙ I.Πβ ∙ un
              ; Πη = λ {Γ} {n} {A} {B} {f} →
                     let
                       (A[p]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.p
                       p⁺ = coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (I.p I.⁺)
                       q' = coe (cong (I.Tm (Γ I.▹ A)) $ un) I.q
                       (B[p⁺]T ,-) = ∣ M.⟦ B ⟧Ty ∣ p⁺
                       (B[p⁺][⟨q⟩]T ,-) = ∣ M.⟦ B[p⁺]T ⟧Ty ∣ I.⟨ q' ⟩
                       (f[p]t ,-) = ∣ M.⟦ f ⟧Tm ∣ (I.p {A = A})
                     in cong I.lamₑ
                          $ refl
                          $ refl
                          $ refl
                          $ (sym un
                           ∙ cong I.[]Tₑ
                               $ (cong I.▹ₑ $ refl $ refl $ sym un)
                               $ refl
                               $ refl
                               $ (sym un
                                ∙ cong I.[]Tₑ
                                    $ refl
                                    $ refl
                                    $ (cong I.▹ₑ $ refl $ refl $ sym un)
                                    $ refl
                                    $ sym coh)
                               $ (cong I.⟨⟩ₑ $ refl $ refl $ sym un $ sym coh))
                          $ (sym coh
                           ∙ cong I.appₑ
                               $ refl
                               $ refl
                               $ sym un
                               $ (sym un ∙ cong I.[]Tₑ
                                             $ refl
                                             $ refl
                                             $ (cong I.▹ₑ $ refl $ refl $ sym un)
                                             $ refl
                                             $ sym coh)
                               $ (sym coh ∙ sym un ∙ coh)
                               $ sym coh)
                      ∙ I.Πη
              ; lam[] = refl
              }
      ; bool = record
                { Bool = I.Bool
                ; Bool[] = refl
                ; true = I.true
                ; false = I.false
                ; true[] = refl
                ; false[] = refl
                ; elim = λ {Γ} {n} A a[true] a[false] b →
                         let
                           (A[b]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ b ⟩
                           (A[true]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ I.true ⟩
                           (A[false]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ I.false ⟩
                         in coe (cong (I.Tm Γ) $ un) (I.elim A (coe (cong (I.Tm Γ) $ sym un) a[true]) (coe (cong (I.Tm Γ) $ sym un) a[false]) b)
                ; elim[] = λ {Γ} {n} {Δ} {A} {a} {b} {c} {γ} →
                           let
                             (A[c]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ c ⟩
                             (Bool[γ]T ,-) = ∣ M.⟦ I.Bool ⟧Ty ∣ γ
                             (A[true]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ I.true ⟩
                             (A[false]T ,-) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ I.false ⟩
                             (a[γ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ
                             (b[γ]t ,-) = ∣ M.⟦ b ⟧Tm ∣ γ
                             (c[γ]t ,-) = ∣ M.⟦ c ⟧Tm ∣ γ
                             (elim[γ]t ,-) = ∣ M.⟦ coe (cong (I.Tm Γ) $ un) (I.elim A (coe (cong (I.Tm Γ) $ sym un) a) (coe (cong (I.Tm Γ) $ sym un) b) c) ⟧Tm ∣ γ
                             (A[γ⁺]T ,-) = ∣ M.⟦ A ⟧Ty ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ refl) $ refl) (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺)))
                             (A[γ⁺][c[γ]]T ,-) = ∣ M.⟦ A[γ⁺]T ⟧Ty ∣ I.⟨ coe (cong (I.Tm Δ) $ refl) c[γ]t ⟩
                           in sym un
                            ∙ cong I.[]tₑ $ refl $ refl $ refl $ sym un $ sym coh $ refl
                            ∙ I.elim[]
                            ∙ {!!}
                            ∙ coh
                ; Boolβ₁ = {!!}
                ; Boolβ₂ = {!!}
                }
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
