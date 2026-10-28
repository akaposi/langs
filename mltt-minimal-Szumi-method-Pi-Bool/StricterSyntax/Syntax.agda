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
               { _∘_ = λ {Δ} {Γ} {Θ} γ δ → L.fst (∣ M.⟦ γ ⟧Sub ∣ δ)
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
                           -- This alone with the normal defintion consumes 120+ GB of RAM
                           -- Giving all implicits reduces RAM usage to just around 50 GB.
                           -- USE let proof = ? in proof; IT REDUCES MEMORY USAGE DRAMMATICALLY
                           --   from these 120 GB down to 17 GB on my laptop.
                           let
                             -- (A[c]T ,ₚ ≈A[c]T) = ∣ M.⟦_⟧Ty {I._▹_ {0} Γ (I.Bool {Γ})} {n} A ∣ {Γ} (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)
                             (A[c]T ,ₚ ≈A[c]T) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ c ⟩
                             -- (Bool[γ]T ,ₚ ≈Bool[γ]T) = ∣ M.⟦_⟧Ty {Γ} {0} (I.Bool {Γ}) ∣ {Δ} γ
                             (Bool[γ]T ,ₚ ≈Bool[γ]T) = ∣ M.⟦ I.Bool ⟧Ty ∣ γ
                             -- (A[true]T ,ₚ ≈A[true]T) = ∣ M.⟦_⟧Ty {I._▹_ {0} Γ (I.Bool {Γ})} {n} A ∣ {Γ} (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))
                             (A[true]T ,ₚ ≈A[true]T) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ I.true ⟩
                             -- (A[false]T ,ₚ ≈A[false]T) = ∣ M.⟦_⟧Ty {I._▹_ {0} Γ (I.Bool {Γ})} {n} A ∣ {Γ} (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))
                             (A[false]T ,ₚ ≈A[false]T) = ∣ M.⟦ A ⟧Ty ∣ I.⟨ I.false ⟩
                             -- (A[true][γ]T ,ₚ ≈A[true][γ]T) = ∣ M.⟦_⟧Ty {Γ} {n} A[true]T ∣ {Δ} γ
                             (A[true][γ]T ,ₚ ≈A[true][γ]T) = ∣ M.⟦ A[true]T ⟧Ty ∣ γ
                             -- (A[false][γ]T ,ₚ ≈A[false][γ]T) = ∣ M.⟦_⟧Ty {Γ} {n} A[false]T ∣ {Δ} γ
                             (A[false][γ]T ,ₚ ≈A[false][γ]T) = ∣ M.⟦ A[false]T ⟧Ty ∣ γ
                             -- (a[γ]t ,ₚ ≈a[γ]t) = ∣ M.⟦_⟧Tm {Γ} {n} {A[true]T} a ∣ {Δ} γ
                             (a[γ]t ,ₚ ≈a[γ]t) = ∣ M.⟦ a ⟧Tm ∣ γ
                             -- (b[γ]t ,ₚ ≈b[γ]t) = ∣ M.⟦_⟧Tm {Γ} {n} {A[false]T} b ∣ {Δ} γ
                             (b[γ]t ,ₚ ≈b[γ]t) = ∣ M.⟦ b ⟧Tm ∣ γ
                             -- (c[γ]t ,ₚ ≈c[γ]t) = ∣ M.⟦_⟧Tm {Γ} {0} {I.Bool {Γ}} c ∣ {Δ} γ
                             (c[γ]t ,ₚ ≈c[γ]t) = ∣ M.⟦ c ⟧Tm ∣ γ
                             -- (elim[γ]t ,ₚ ≈elim[γ]t) = ∣ M.⟦_⟧Tm {Γ} {n} {A[c]T} (coe {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {I.Tm Γ {n} A[c]T} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set lzero} {λ _ → Set lzero} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set lzero} (I.Tm Γ {n})) {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} {A[c]T} ≈A[c]T) (I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set lzero} {λ _ → Set lzero} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set lzero} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set lzero} {λ _ → Set lzero} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set lzero} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c)) ∣ {Δ} γ
                             (elim[γ]t ,ₚ ≈elim[γ]t) = ∣ M.⟦ coe (cong (I.Tm Γ) $ ≈A[c]T) (I.elim A (coe (cong (I.Tm Γ) $ sym ≈A[true]T) a) (coe (cong (I.Tm Γ) $ sym ≈A[false]T) b) c) ⟧Tm ∣ γ
                             -- (A[γ⁺]T ,ₚ ≈A[γ⁺]T) = ∣ M.⟦_⟧Ty {I._▹_ {0} Γ (I.Bool {Γ})} {n} A ∣ {I.▹ₑ 0 Δ Bool[γ]T} (coe {lzero} {I.Sub (I.▹ₑ 0 Δ Bool[γ]T) (I._▹_ {0} Γ (I.Bool {Γ}))} {I.Sub (I.▹ₑ 0 Δ Bool[γ]T) (I._▹_ {0} Γ (I.Bool {Γ}))} (_$_ {lzero} {I.Con} {lsuc lzero} {I.Con} {λ _ → Set lzero} {λ _ → Set lzero} {I.Sub (I.▹ₑ 0 Δ Bool[γ]T)} {I.Sub (I.▹ₑ 0 Δ Bool[γ]T)} (_$_ {lzero} {I.Con} {lsuc lzero} {I.Con} {λ _ → I.Con → Set lzero} {λ _ → I.Con → Set lzero} {I.Sub} {I.Sub} (cong {lsuc lzero} {I.Con → I.Con → Set lzero} I.Sub) {I.▹ₑ 0 Δ Bool[γ]T} {I.▹ₑ 0 Δ Bool[γ]T} (_$_ {lzero} {I.Ty Δ 0} {lzero} {I.Ty Δ 0} {λ _ → I.Con} {λ _ → I.Con} {I.▹ₑ 0 Δ} {I.▹ₑ 0 Δ} (_$_ {lzero} {I.Con} {lzero} {I.Con} {λ z → (A₁ : I.Ty z 0) → I.Con} {λ z → (A₁ : I.Ty z 0) → I.Con} {I.▹ₑ 0} {I.▹ₑ 0} (_$_ {lzero} {ℕ} {lzero} {ℕ} {λ z → (Γ₁ : I.Con) (A₁ : I.Ty Γ₁ z) → I.Con} {λ z → (Γ₁ : I.Con) (A₁ : I.Ty Γ₁ z) → I.Con} {I.▹ₑ} {I.▹ₑ} (cong {lzero} {(n₁ : ℕ) (Γ₁ : I.Con) (A₁ : I.Ty Γ₁ n₁) → I.Con} I.▹ₑ) {0} {0} refl) {Δ} {Δ} refl) {Bool[γ]T} {Bool[γ]T} refl)) {I._▹_ {0} Γ (I.Bool {Γ})} {I._▹_ {0} Γ (I.Bool {Γ})} refl) (coe {lzero} {I.Sub (I.▹ₑ 0 Δ (I._[_]T {Γ} {0} {Δ} (I.Bool {Γ}) γ)) (I._▹_ {0} Γ (I.Bool {Γ}))} {I.Sub (I.▹ₑ 0 Δ Bool[γ]T) (I._▹_ {0} Γ (I.Bool {Γ}))} (_$_ {lzero} {I.Con} {lsuc lzero} {I.Con} {λ _ → Set lzero} {λ _ → Set lzero} {I.Sub (I.▹ₑ 0 Δ (I._[_]T {Γ} {0} {Δ} (I.Bool {Γ}) γ))} {I.Sub (I.▹ₑ 0 Δ Bool[γ]T)} (_$_ {lzero} {I.Con} {lsuc lzero} {I.Con} {λ _ → I.Con → Set lzero} {λ _ → I.Con → Set lzero} {I.Sub} {I.Sub} (cong {lsuc lzero} {I.Con → I.Con → Set lzero} I.Sub) {I.▹ₑ 0 Δ (I._[_]T {Γ} {0} {Δ} (I.Bool {Γ}) γ)} {I.▹ₑ 0 Δ Bool[γ]T} (_$_ {lzero} {I.Ty Δ 0} {lzero} {I.Ty Δ 0} {λ _ → I.Con} {λ _ → I.Con} {I.▹ₑ 0 Δ} {I.▹ₑ 0 Δ} (_$_ {lzero} {I.Con} {lzero} {I.Con} {λ z → (A₁ : I.Ty z 0) → I.Con} {λ z → (A₁ : I.Ty z 0) → I.Con} {I.▹ₑ 0} {I.▹ₑ 0} (_$_ {lzero} {ℕ} {lzero} {ℕ} {λ z → (Γ₁ : I.Con) (A₁ : I.Ty Γ₁ z) → I.Con} {λ z → (Γ₁ : I.Con) (A₁ : I.Ty Γ₁ z) → I.Con} {I.▹ₑ} {I.▹ₑ} (cong {lzero} {(n₁ : ℕ) (Γ₁ : I.Con) (A₁ : I.Ty Γ₁ n₁) → I.Con} I.▹ₑ) {0} {0} refl) {Δ} {Δ} refl) {I._[_]T {Γ} {0} {Δ} (I.Bool {Γ}) γ} {Bool[γ]T} ≈Bool[γ]T)) {I._▹_ {0} Γ (I.Bool {Γ})} {I._▹_ {0} Γ (I.Bool {Γ})} refl) (I._⁺ {Δ} {Γ} {0} {I.Bool {Γ}} γ)))
                             (A[γ⁺]T ,ₚ ≈A[γ⁺]T) = ∣ M.⟦ A ⟧Ty ∣ (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ refl) $ refl) (coe (cong I.Sub $ (cong I.▹ₑ $ refl $ refl $ un) $ refl) (γ I.⁺)))
                             -- (A[γ⁺][c[γ]]T ,ₚ ≈A[γ⁺][c[γ]]T) = ∣ M.⟦_⟧Ty {I.▹ₑ 0 Δ Bool[γ]T} {n} A[γ⁺]T ∣ {Δ} (I.⟨_⟩ {Δ} {0} {Bool[γ]T} (coe {lzero} {I.Tm Δ {0} Bool[γ]T} {I.Tm Δ {0} Bool[γ]T} (_$_ {lzero} {I.Ty Δ 0} {lsuc lzero} {I.Ty Δ 0} {λ _ → Set lzero} {λ _ → Set lzero} {I.Tm Δ {0}} {I.Tm Δ {0}} (cong {lsuc lzero} {I.Ty Δ 0 → Set lzero} (I.Tm Δ {0})) {Bool[γ]T} {Bool[γ]T} refl) c[γ]t))
                             (A[γ⁺][c[γ]]T ,ₚ ≈A[γ⁺][c[γ]]T) = ∣ M.⟦ A[γ⁺]T ⟧Ty ∣ I.⟨ coe (cong (I.Tm Δ) $ refl) c[γ]t ⟩
                             -- (A[γ⁺][true]T ,ₚ ≈A[γ⁺][true]T) = ∣ M.⟦_⟧Ty {I.▹ₑ 0 Δ Bool[γ]T} {n} A[γ⁺]T ∣ {Δ} (I.⟨_⟩ {Δ} {0} {Bool[γ]T} (I.true {Δ}))
                             (A[γ⁺][true]T ,ₚ ≈A[γ⁺][true]T) = ∣ M.⟦ A[γ⁺]T ⟧Ty ∣ I.⟨ I.true ⟩
                             -- (A[γ⁺][false]T ,ₚ ≈A[γ⁺][false]T) = ∣ M.⟦_⟧Ty {I.▹ₑ 0 Δ Bool[γ]T} {n} A[γ⁺]T ∣ {Δ} (I.⟨_⟩ {Δ} {0} {Bool[γ]T} (I.false {Δ}))
                             (A[γ⁺][false]T ,ₚ ≈A[γ⁺][false]T) = ∣ M.⟦ A[γ⁺]T ⟧Ty ∣ I.⟨ I.false ⟩
                             -- pr1 = _$_ {lzero} {I.Sub Δ Γ} {lzero} {I.Sub Δ Γ} {λ z → I.Tm Δ {n} (I._[_]T {Γ} {n} {Δ} A[c]T z)} {λ z → I.Tm Δ {n} (I._[_]T {Γ} {n} {Δ} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)) z)} {I.[]tₑ Γ Δ n A[c]T (coe {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {I.Tm Γ {n} A[c]T} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} {A[c]T} ≈A[c]T) (I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c))} {I.[]tₑ Γ Δ n (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)) (I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c)} (_$_ {lzero} {I.Tm Γ {n} A[c]T} {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {λ _ → (γ₁ : I.Sub Δ Γ) → I.Tm Δ {n} (I._[_]T {Γ} {n} {Δ} A[c]T γ₁)} {λ _ → (γ₁ : I.Sub Δ Γ) → I.Tm Δ {n} (I._[_]T {Γ} {n} {Δ} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)) γ₁)} {I.[]tₑ Γ Δ n A[c]T} {I.[]tₑ Γ Δ n (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} (_$_ {lzero} {I.Ty Γ n} {lzero} {I.Ty Γ n} {λ z → (a₁ : I.Tm Γ {n} z) (γ₁ : I.Sub Δ Γ) → I.Tm Δ {n} (I._[_]T {Γ} {n} {Δ} z γ₁)} {λ z → (a₁ : I.Tm Γ {n} z) (γ₁ : I.Sub Δ Γ) → I.Tm Δ {n} (I._[_]T {Γ} {n} {Δ} z γ₁)} {I.[]tₑ Γ Δ n} {I.[]tₑ Γ Δ n} (_$_ {lzero} {ℕ} {lzero} {ℕ} {λ z → (A₁ : I.Ty Γ z) (a₁ : I.Tm Γ {z} A₁) (γ₁ : I.Sub Δ Γ) → I.Tm Δ {z} (I._[_]T {Γ} {z} {Δ} A₁ γ₁)} {λ z → (A₁ : I.Ty Γ z) (a₁ : I.Tm Γ {z} A₁) (γ₁ : I.Sub Δ Γ) → I.Tm Δ {z} (I._[_]T {Γ} {z} {Δ} A₁ γ₁)} {I.[]tₑ Γ Δ} {I.[]tₑ Γ Δ} (_$_ {lzero} {I.Con} {lzero} {I.Con} {λ z → (n₁ : ℕ) (A₁ : I.Ty Γ n₁) (a₁ : I.Tm Γ {n₁} A₁) (γ₁ : I.Sub z Γ) → I.Tm z {n₁} (I._[_]T {Γ} {n₁} {z} A₁ γ₁)} {λ z → (n₁ : ℕ) (A₁ : I.Ty Γ n₁) (a₁ : I.Tm Γ {n₁} A₁) (γ₁ : I.Sub z Γ) → I.Tm z {n₁} (I._[_]T {Γ} {n₁} {z} A₁ γ₁)} {I.[]tₑ Γ} {I.[]tₑ Γ} (_$_ {lzero} {I.Con} {lzero} {I.Con} {λ z → (Δ₁ : I.Con) (n₁ : ℕ) (A₁ : I.Ty z n₁) (a₁ : I.Tm z {n₁} A₁) (γ₁ : I.Sub Δ₁ z) → I.Tm Δ₁ {n₁} (I._[_]T {z} {n₁} {Δ₁} A₁ γ₁)} {λ z → (Δ₁ : I.Con) (n₁ : ℕ) (A₁ : I.Ty z n₁) (a₁ : I.Tm z {n₁} A₁) (γ₁ : I.Sub Δ₁ z) → I.Tm Δ₁ {n₁} (I._[_]T {z} {n₁} {Δ₁} A₁ γ₁)} {I.[]tₑ} {I.[]tₑ} (cong {lzero} {(Γ₁ Δ₁ : I.Con) (n₁ : ℕ) (A₁ : I.Ty Γ₁ n₁) (a₁ : I.Tm Γ₁ {n₁} A₁) (γ₁ : I.Sub Δ₁ Γ₁) → I.Tm Δ₁ {n₁} (I._[_]T {Γ₁} {n₁} {Δ₁} A₁ γ₁)} I.[]tₑ) {Γ} {Γ} refl) {Δ} {Δ} refl) {n} {n} refl) {A[c]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} {A[c]T} ≈A[c]T)) {coe {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {I.Tm Γ {n} A[c]T} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} {A[c]T} ≈A[c]T) (I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c)} {I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c} (sym {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {I.Tm Γ {n} A[c]T} {I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c} {coe {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {I.Tm Γ {n} A[c]T} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} {A[c]T} ≈A[c]T) (I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c)} (coh {lzero} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c))} {I.Tm Γ {n} A[c]T} {I.elim {Γ} {n} A (coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a) (coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b) c} {_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} c)} {A[c]T} ≈A[c]T}))) {γ} {γ} refl
                             pr1 = cong I.[]tₑ $ refl $ refl $ refl $ sym ≈A[c]T $ sym coh $ refl
                             -- pr2 = I.elim[] {Γ} {n} {Δ} {A} {coe {lzero} {I.Tm Γ {n} A[true]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[true]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.true {Γ}))} {A[true]T} ≈A[true]T)) a} {coe {lzero} {I.Tm Γ {n} A[false]T} {I.Tm Γ {n} (I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ})))} (_$_ {lzero} {I.Ty Γ n} {lsuc lzero} {I.Ty Γ n} {λ _ → Set} {λ _ → Set} {I.Tm Γ {n}} {I.Tm Γ {n}} (cong {lsuc lzero} {I.Ty Γ n → Set} (I.Tm Γ {n})) {A[false]T} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} (sym {lzero} {I.Ty Γ n} {I.Ty Γ n} {I._[_]T {I._▹_ {0} Γ (I.Bool {Γ})} {n} {Γ} A (I.⟨_⟩ {Γ} {0} {I.Bool {Γ}} (I.false {Γ}))} {A[false]T} ≈A[false]T)) b} {c} {γ}
                             pr2 = I.elim[] {γ = γ}
                             pr3 = cong I.elimₑ $ refl $ refl $ (cong I.[]Tₑ $ refl $ refl $ refl $ refl $ coh ∙ un) $ (sym (coh) ∙ cong I.[]tₑ $ refl $ refl $ refl $ un $ sym (coh) $ refl ∙ un ∙ coh ∙ coh) $ (sym (coh) ∙ cong I.[]tₑ $ refl $ refl $ refl $ un $ sym (coh) $ refl ∙ un ∙ coh ∙ coh) $ (sym (coh) ∙ un ∙ coh)
                             t1 = I.elim A[γ⁺]T (coe (cong (I.Tm Δ) $ sym ≈A[γ⁺][true]T) (coe (cong (I.Tm Δ) $ (sym ≈A[true][γ]T ∙ (cong I.[]Tₑ $ refl $ refl $ refl $ sym ≈A[true]T $ refl ∙ I.weave (I.⟨⟩∘ ∙ cong I.∘ₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ ≈Bool[γ]T) $ refl $ (coh ∙ coh) $ (cong I.⟨⟩ₑ $ refl $ refl $ ≈Bool[γ]T $ I.true[])) ∙ cong I.[]Tₑ $ refl $ refl $ refl $ ≈A[γ⁺]T $ refl) ∙ ≈A[γ⁺][true]T)) a[γ]t)) (coe (cong (I.Tm Δ) $ sym ≈A[γ⁺][false]T) (coe (cong (I.Tm Δ) $ (sym ≈A[false][γ]T ∙ (cong I.[]Tₑ $ refl $ refl $ refl $ sym ≈A[false]T $ refl ∙ I.weave (I.⟨⟩∘ ∙ cong I.∘ₑ $ refl $ (cong I.▹ₑ $ refl $ refl $ ≈Bool[γ]T) $ refl $ (coh ∙ coh) $ (cong I.⟨⟩ₑ $ refl $ refl $ ≈Bool[γ]T $ I.false[])) ∙ cong I.[]Tₑ $ refl $ refl $ refl $ ≈A[γ⁺]T $ refl) ∙ ≈A[γ⁺][false]T)) b[γ]t)) (coe (cong (I.Tm Δ) $ (sym ≈Bool[γ]T ∙ I.Bool[])) c[γ]t)
                             {-
                             proof = sym ≈elim[γ]t
                                   ∙ pr1
                                   ∙ pr2
                                   ∙ pr3
                                   ∙ coh {lzero}
                                         {I.Tm Δ {n} (I._[_]T {I._▹_ {0} Δ (I.Bool {Δ})} {n} {Δ} A[γ⁺]T (I.⟨_⟩ {Δ} {0} {I.Bool {Δ}} (coe {lzero} {I.Tm Δ {0} Bool[γ]T} {I.Tm Δ {0} (I.Bool {Δ})} (_$_ {lzero} {I.Ty Δ 0} {lsuc lzero} {I.Ty Δ 0} {λ _ → Set lzero} {λ _ → Set lzero} {I.Tm Δ {0}} {I.Tm Δ {0}} (cong {lsuc lzero} {I.Ty Δ 0 → Set lzero} (I.Tm Δ {0})) {Bool[γ]T} {I.Bool {Δ}} refl) c[γ]t)))}
                                         {I.Tm Δ A[γ⁺][c[γ]]T}
                                         {t1}
                                         {cong (I.Tm Δ) $ ≈A[γ⁺][c[γ]]T}
                             -}
                             proof = sym ≈elim[γ]t
                                   ∙ pr1
                                   ∙ pr2
                                   ∙ pr3
                                   ∙ coh {a₀ = t1} {e = cong (I.Tm Δ) $ ≈A[γ⁺][c[γ]]T}
                           in proof
                ; Boolβ₁ = λ {n} {Γ} {A} {a} {b} → sym coh ∙ I.Boolβ₁ ∙ sym coh
                ; Boolβ₂ = λ {n} {Γ} {A} {a} {b} → sym coh ∙ I.Boolβ₂ ∙ sym coh
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
app[]ₛ {Γ} {Δ} {n} {A} {B} {f} {a} {γ} =
  let
    (A[γ]T ,-) = ∣ M.⟦ A ⟧Ty ∣ γ
    (B[γ⁺]T ,-) = ∣ M.⟦ B ⟧Ty ∣ (coe (cong I.Sub $ (cong (Δ I.▹_) $ un) $ refl) (γ I.⁺))
    (B[a]T ,-) = ∣ M.⟦ B ⟧Ty ∣ I.⟨ a ⟩
    (f[γ]t ,-) = ∣ M.⟦ f ⟧Tm ∣ γ
    (a[γ]t ,-) = ∣ M.⟦ a ⟧Tm ∣ γ
    (app-f-a[γ]t ,-) = ∣ M.⟦ Iₛ.app f a ⟧Tm ∣ γ
  in sym un ∙ cong I.[]tₑ $ refl $ refl $ refl $ sym un $ sym coh $ refl ∙ I.app[] ∙ cong I.appₑ $ refl $ refl $ un $ (cong I.[]Tₑ $ refl $ refl $ (cong (Δ I.▹_) $ un) $ refl $ coh ∙ un) $ (sym I.[]Π ∙ un) $ un ∙ coh ∙ coh
