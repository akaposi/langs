{-# OPTIONS --prop --rewriting --with-K --confluence-check --no-postfix-projections --hidden-argument-puns #-}

module Dictatorship.QIIRT.Syntax where

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
open import Dictatorship.QIIRT.Sigma
open import Dictatorship.QIIRT.Pi
open import Dictatorship.QIIRT.Empty
open import Dictatorship.QIIRT.Bool

{-
D : DepModel {lzero} {lzero} {lzero}
D = DepModel.constructor
      (Sorts∙.constructor
        Con∙'
        Sub∙'
        Ty∙'
        Tm∙'
      )
      (CwF∙.constructor
        ∘∙'
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (Sigma∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (Pi∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (Empty∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
      )
      (BoolT∙.constructor
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
        {!!}
      )
-}

{-
D-ből és I-ből összerakni egy Iₛ-t (strict syntax, ahol az Iₛ-be az I-ből válogatjuk össze a dolgokat,
kivéve a helyettesítési szabályt, amit a D-ből szedünk össze.)
-}
