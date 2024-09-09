# QIIT book

Everything in Cubical Agda. For each language, separate files: Syntax,
DepModel(with induction), Model(with iteration -- derived using
DepModel). In syntaxes, we never use transport, but PathP is fine. We
use the standard cubical library. If you finished a project, you are
allowed to change the - to +!

The point of this is that we can suggest projects to students from
below.

- untyped-sk: untyped SK combinator calculus (Janet)
  - QIIT syntax
  - no finite model
  - one-step parallel rewriting model, S ≠ K
  - Engeler's infinite model
- typed-sk: Typed SK combinator calculus (Janet, copy from typesystems)
  - QIIT syntax
  - standard model
  - normalisation proof
- typed-extensional-sk
  - equivalence with stlc
- stlc-minimal: simply typed lambda calculus with ⇒,ι (typesystems)
  - QIIT syntax, single substitution calculus
    - derive parallel stuff
    - standard model
  - QIIT syntax, parallel substitution calculus
    - standard model
    - elaborator (see https://github.com/Seeker04/stlc-agda-elab )
  - strictification of _[_] and _∘_
    - canonicity
    - normalisation
  - prefascist stricification
- system-t
  - elaborator
  - normalisation
  - prove that an internal System T evaluator is not definable (see typesystems repo)
- stlc-big: STLC with 0,1,+,*,⇒, general inductive types, general coinductive types (typesystems, Mihocs Oliver)
  - elaborator
  - QIIT syntax parallel substitution
  - strictification of _[_] and _∘_
    - standard model
    - canonicity
    - normalisation
- fol-minimal: first-order logic with ⇒, binary relation symbol (Samy mostly did this)
  - elaborator
  - QIIT syntax, parallel
  - definable quotient = strictification (no need for higher inductive types), double-contexts for the syntax, derive the usual one with two context extensions
  - Bool, Prop (Tarski), Kripke models, Beth models
  - normalisation
  - show that LEM is not derivable via normalisation
  - completeness of Kripke models
- fol-big: first-order logic (Samy was working on this) with all the logical connectives
  - elaborator
  - QIIT syntax, parallel
  - definable quotient here as well
  - same models as fol-minimal
  - completeness for Beth models
- system-f
  - elaborator
  - QIIT syntax, parallel, merged contexts
  - strictification
  - model with type-in-type
- mltt-minimal: Π,U,El,cd
  - elaborator
  - QIIT syntax, parallel
    - standard model
    - model which negates funext (PMP's model, Andras formalised it)
    - family model
    - prop model
    - setoid model
    - groupoid model
    - presheaf model
    - ×Bool model
  - strictification of _[_] and _∘_
    - canonicity
    - normalisation, injectivity of Π, injectivity and disjointness of constructors (externally)
    - gluing dependent/displayed model over the syntax
      - show parametricity as a special case
- mltt-finite: Π,Σ,⊥,⊤,Bool, lots of η, we cannot have large elim for Bool
  - elaborator
  - QIIT syntax, parallel
    - standard model
    - Bool model
    - finite model
  - strictification of _[_] and _∘_
    - canonicity
    - normalisation
- mltt-big: Π,Σ,⊥,⊤,Bool,Id,W,M,U(Coquand)  <- basically Agda/predicative Coq
  - elaborator
  - QIIT syntax, parallel
    - standard model
  - strictification of _[_] and _∘_
    - canonicity
    - normalisation
- sett: setoid type theory/OTT with symmetric inductive and coinductive types
  - elaborator
  - setoid model, justifies funext
- sett-qiit: setoid type theory with all QIITs using ToS specification
  - elaborator
  - setoid model, justifies funext
- cubical type theory
- H.O.T.T.
