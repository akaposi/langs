{-# OPTIONS --cubical #-}

open import Agda.Primitive


module typed-sk.StandardModel where

open import typed-sk.Model

-- St : Model
-- St = record
--   { Ty  = Set
--   ; Tm  = λ A → A
--   ; ι   = Lift ⊤
--   ; _⇒_ = λ A B → A → B
--   ; _$_ = λ f x → f x
--   ; K   = λ x y → x
--   ; S   = λ x y z → x z (y z)
--   ; Kβ  = refl
--   ; Sβ  = refl
--   }
-- module St = Model St