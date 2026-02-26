{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty renaming (rec to exfalso) 
open import Cubical.Foundations.HLevels
module stlc-sum.InitialModel where

import stlc-sum.Model as Mod

open import stlc-sum.Syntax

In : Mod.Model
In .Mod.Model.Con = Con
In .Mod.Model.Sub = Sub
In .Mod.Model.SubSet = SubSet
In .Mod.Model._∘_ = _∘_
In .Mod.Model.assoc = assoc
In .Mod.Model.id = id
In .Mod.Model.idr = idr
In .Mod.Model.idl = idl
In .Mod.Model.Ty = Ty
In .Mod.Model.Tm = Tm
In .Mod.Model.TmSet = TmSet
In .Mod.Model._[_] = _[_]
In .Mod.Model.[]-∘ = []-∘
In .Mod.Model.[]-id = []-id
In .Mod.Model._▸_ = _▸_
In .Mod.Model.p = p
In .Mod.Model.q = q
In .Mod.Model._,_ = _,_
In .Mod.Model.,-∘ = ,-∘
In .Mod.Model.▸-β₁ = ▸-β₁
In .Mod.Model.▸-β₂ = ▸-β₂
In .Mod.Model.▸-η = ▸-η
In .Mod.Model.◆ = ◆
In .Mod.Model.ε = ε
In .Mod.Model.ε-∘ = ε-∘
In .Mod.Model.◆-η = ◆-η
In .Mod.Model.⊥ₗ = ⊥ₗ
In .Mod.Model.Unitₗ = Unitₗ
In .Mod.Model._⇒_ = _⇒_
In .Mod.Model._+ₗ_ = _+ₗ_
In .Mod.Model.app = app
In .Mod.Model.app-[] = app-[]
In .Mod.Model.lam = lam
In .Mod.Model.lam-[] = lam-[]
In .Mod.Model.⇒-β = ⇒-β
In .Mod.Model.⇒-η = ⇒-η
In .Mod.Model.exfalsoₗ = exfalsoₗ
In .Mod.Model.exfalsoₗ-[] = exfalsoₗ-[]
In .Mod.Model.ttₗ = ttₗ
In .Mod.Model.ttₗ-[] = ttₗ-[]
In .Mod.Model.unit-η = unit-η
In .Mod.Model.inlₗ = inlₗ
In .Mod.Model.inlₗ-[] = inlₗ-[]
In .Mod.Model.inrₗ = inrₗ
In .Mod.Model.inrₗ-[] = inrₗ-[]
In .Mod.Model.case+ = case+
In .Mod.Model.case+[] = case+[]
In .Mod.Model.+-β₁ = +-β₁
In .Mod.Model.+-β₂ = +-β₂

-- -- In .Mod.Model.+-η = +-η