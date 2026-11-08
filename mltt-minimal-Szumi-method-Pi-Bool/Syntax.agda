{-# OPTIONS --prop --rewriting --with-K #-}

module Syntax where

open import Agda.Primitive
open import Model

postulate
  I : Model {lzero} {lzero} {lzero}

module I = Model.Model I
