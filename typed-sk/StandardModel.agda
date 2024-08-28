{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to exfalso) 
open import Cubical.Foundations.HLevels
module typed-sk.StandardModel where

open import typed-sk.Model

St : {l : Level} → (A : hSet l) → Model
St {l} A = record
     { Ty = hSet l; 
       ι = A; 
       _⇒_ = λ ty₁ ty₂ → ((x : fst ty₁) → fst ty₂) , isSetΠ (λ x → snd ty₂); 
       Tm = λ x → fst x ;
       TmSet = λ {x} → snd x ; 
       _·_ = λ x x₁ → x x₁; 
       K = λ {A₁} {B} → λ a b → a; 
       S = λ a b c → a c (b c); 
       Kβ =  λ t u i → t;
       Sβ = λ t u v i → t v (u v)}
