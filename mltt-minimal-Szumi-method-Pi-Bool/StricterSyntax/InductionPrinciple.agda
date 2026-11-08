{-# OPTIONS --prop --rewriting --with-K --confluence-check --hidden-argument-puns #-}

open import StricterSyntax.Syntax
open import DepModel Iₛ

module StricterSyntax.InductionPrinciple {i} {j} {k} (D : DepModel {i} {j} {k}) where

open import Lib

open Iₛ

open DepModel D

