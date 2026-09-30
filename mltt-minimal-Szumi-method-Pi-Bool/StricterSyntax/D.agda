{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module StricterSyntax.D where

open import Lib
open import Syntax
open import DepModel
open I

open import StricterSyntax.Sorts
open Con∙
open Sub∙
open Ty∙
open Tm∙

open import StricterSyntax.CwF
open import StricterSyntax.Lift
open import StricterSyntax.U
open import StricterSyntax.Pi
open import StricterSyntax.Bool

D : DepModel {lzero} {lzero} {lzero}
D = record
     { sorts∙ = record { StricterSyntax.Sorts }
     ; cwf∙ = record
               { StricterSyntax.CwF
               ; ass∙ = λ {Γ}{Δ}{Γ∙}{Δ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙}{Ξ}{Ξ∙}{θ}{θ∙} → ass∙ {Γ}{Δ}{Γ∙}{Δ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙}{Ξ}{Ξ∙}{θ}{θ∙}
               ; [∘]T∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙} → [∘]T∙ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙}
               ; [∘]t∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙}{Θ}{δ}{Θ∙}{δ∙} → [∘]t∙ {Γ}{Γ∙}{n}{A}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙}{Θ}{Θ∙}{δ}{δ∙}
               ; p∙ = λ {Γ}{n}{Γ∙}{A}{A∙} → p∙ {Γ}{n}{Γ∙}{A}{A∙} 
               ; q∙ = λ {Γ}{Γ∙}{n}{A}{A∙} → q∙ {Γ}{Γ∙}{n}{A}{A∙}
               ; _⁺∙ = λ {Δ}{Δ∙}{Γ}{Γ∙}{γ}{n}{A}{A∙} → _⁺∙ {Δ}{Δ∙}{Γ}{Γ∙}{γ}{n}{A}{A∙}
               ; ∘⁺∙ = λ {Δ}{Δ∙}{Γ}{γ}{Γ∙}{γ∙}{Θ}{δ}{Θ∙}{δ∙}{n}{A}{A∙} → ∘⁺∙ {Δ}{Δ∙}{Γ}{γ}{Γ∙}{γ∙}{Θ}{δ}{Θ∙}{δ∙}{n}{A}{A∙}
               ; id⁺∙ = λ {Γ}{n}{A}{Γ∙}{A∙} → id⁺∙ {Γ}{n}{A}{Γ∙}{A∙}
               ; ⟨⟩∘∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙} → ⟨⟩∘∙ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙}
               ; p∘⁺∙ = λ {Δ}{Γ}{Γ∙}{γ}{Δ∙}{γ∙}{n}{A}{A∙} → p∘⁺∙ {Δ}{Γ}{Γ∙}{γ}{Δ∙}{γ∙}{n}{A}{A∙}
               ; p∘⟨⟩∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙} → p∘⟨⟩∙ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}
               ; q[⁺]∙ = λ {Γ}{Γ∙}{Δ}{γ}{Δ∙}{γ∙}{n}{A}{A∙} → q[⁺]∙ {Γ}{Γ∙}{Δ}{γ}{Δ∙}{γ∙}{n}{A}{A∙}
               ; q[⟨⟩]∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙} → q[⟨⟩]∙ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}
               ; ▹η∙ = λ {Γ}{Γ∙}{n}{A}{A∙} → ▹η∙ {Γ}{Γ∙}{n}{A}{A∙}
               }
     ; liftT∙ = record
                 { StricterSyntax.Lift
                 ; Liftη∙ = λ {Γ}{Γ∙}{n}{A}{a}{A∙}{a∙} → Liftη∙ {Γ}{Γ∙}{n}{A}{a}{A∙}{a∙}
                 ; Lift[]∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙} → Lift[]∙ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙}
                 ; lift[]∙ = λ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙} → lift[]∙ {Γ}{n}{A}{Γ∙}{A∙}{a}{a∙}{Δ}{Δ∙}{γ}{γ∙}
                 }
     ; uT∙ = record
              { StricterSyntax.U
              ; U[]∙ = λ {n}{Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙} → U[]∙ {n}{Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙}
              ; cd[]∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙} → cd[]∙ {Γ}{Γ∙}{n}{A}{A∙}{Δ}{Δ∙}{γ}{γ∙}
              }
     ; pi∙ = record
              { StricterSyntax.Pi
              ; Π[]∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{Δ}{Δ∙}{γ}{γ∙} → Π[]∙ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{Δ}{Δ∙}{γ}{γ∙}
              ; lam∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{b} → lam∙ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{b}
              ; app∙ = λ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{f}{a} → app∙ {Γ}{Γ∙}{n}{A}{A∙}{B}{B∙}{f}{a}
              ; Πβ∙ = λ {Γ}{n}{A}{B}{Γ∙}{A∙}{B∙}{b}{b∙}{a}{a∙} → Πβ∙ {Γ}{n}{A}{B}{Γ∙}{A∙}{B∙}{b}{b∙}{a}{a∙}
              ; Πη∙ = λ {Γ}{Γ∙}{n}{A}{B}{f}{A∙}{B∙}{f∙} → Πη∙ {Γ}{Γ∙}{n}{A}{B}{f}{A∙}{B∙}{f∙}
              ; lam[]∙ = λ {Γ}{n}{A}{B}{Γ∙}{A∙}{B∙}{b}{b∙}{Δ}{Δ∙}{γ}{γ∙} → lam[]∙ {Γ}{n}{A}{B}{Γ∙}{A∙}{B∙}{b}{b∙}{Δ}{Δ∙}{γ}{γ∙}
              }
     ; bool∙ = record
                { StricterSyntax.Bool
                ; Bool[]∙ = λ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙} → Bool[]∙ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙}
                ; true[]∙ = λ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙} → true[]∙ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙}
                ; false[]∙ = λ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙} → false[]∙ {Δ}{Γ}{Δ∙}{Γ∙}{γ}{γ∙}
                ; elim[]∙ = λ {Γ} {Δ} {n} {A} {a} {b} {c} {γ} {Γ∙} {Δ∙} {A∙} {a∙} {b∙} {c∙} {γ∙} → elim[]∙ {Γ} {Δ} {n} {A} {a} {b} {c} {γ} {Γ∙} {Δ∙} {A∙} {a∙} {b∙} {c∙} {γ∙}
                ; Boolβ₁∙ = λ {Γ} {n} {A} {Γ∙} {A∙} {a} {a∙} {b} {b∙} → Boolβ₁∙ {Γ} {n} {A} {Γ∙} {A∙} {a} {a∙} {b} {b∙}
                ; Boolβ₂∙ = λ {Γ} {n} {A} {Γ∙} {A∙} {a} {a∙} {b} {b∙} → Boolβ₂∙ {Γ} {n} {A} {Γ∙} {A∙} {a} {a∙} {b} {b∙}
                }
     }
