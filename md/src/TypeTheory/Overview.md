
Overview of Type Theory
===

Proof assistants require computer-interpretable definitions of
everything in mathematics, from sets to numbers to topology, algebra and geometry.

All such definitions have to be built from simpler definitions, all the way down to
some kind of axiomatic foundation.

Even prior to proof assistants, mathematicians were concerned with providing
a foundation for mathematics.
- Euclid for example was the first to axiomize Geometry.
- Later Cantor introduce Set Theory as a way to build modern mathematics.

Type theory was introduced as a foundation for computation and reasoning, and eventually
served as the basis of proof assistants like Coq, Rocq, Agda, Lean, and others.
- Alonzo Church : The simply typed λ-Calculus (1940)
- Per Martin-Löf : Intuitionistic type theory (1972)
- Thierry Coqrand : Calculus of Constructions and Coq (1988)

Foundations
===

Two main foundations exist for mathematics.

- ***Set Theory***
    - Everything is a set.
    - For example, 0, 1, 2, ... = {}, {{}}, {{{}}}, ...
    - Many flavors
    - Not always constructive

- ***Type Theory***
    - Objects are types or terms that have types
    - Is generalluy constructive
    - Many flavors: COC, CIC, HOTT, Cubical, ...

Lean's Type Theory
===

Lean's Type theory consists of:

- Typed Lambda Calculus / Arrow Types
- Dependent types
  - Π x : T, M x
  - ∀ x : T, P x
  - Arrow types are actually a special case of dependent types
  - Gives you parametric polymoprhism
- Type universes
  - Prop   := Sort 0
  - Type u := Sort (u+1)
  - Prop : Type 0 : Type 1 : Type 2 : ...
  - Allows Types do depend on Types
  - Can have type and univerrse polymorphism
- Prop
  - Impredicative:
    ```∀ P : Prop, P → P``` ok. So you can define And (p : Prop) (q: Prop) : Prop
    ```∀ T : Type u, T → T : Type (u + 1)``` requires universe levels
  - Proof irrelevant: if hp : p and hq : p then hp = hq (And would be possible but awkward without impredicativity)
- Inductive Types (natural deduction-style presentation)
  - Formation
  - Introduction
  - Elimination
  - Computation
  - Strict positivity
- Conversion and reduction
  - β reduction
  - η-conversion
  - δ-reduction
  - ι-reduction
- Definitional Equality
  - If the above conversions and reductions result in the same thing for two terms, then the terms are equal
  - Complicated Prop valued types may be propositionally equal (not definitionally equal) and require proofs
- Type checking and inference
  - Holes / sorrys
  - Implicit and explicity paramters
- Quotients
- A sophisticaed elaborator
  - User defined syntax and macros
  - Typeclasses and instances



Example of Dependent Types
===




```lean
-- A type-level function that is universe polymorphic
def Pair.{u, v} (α : Type u) (β : Type v) : Type (max u v) :=
  Prod α β

#check Pair Nat Bool          -- Type
#check List Nat
#check Pair (List Nat) Nat      -- Type 1



def Compose.{u, v, w}
    (F : Type v → Type w) (G : Type u → Type v) : Type u → Type w :=
  fun α => F (G α)

#check Compose Option List Nat  -- Option (List Nat)


def Arrow.{u, v} (α : Type u) (β : Type v) : Type (max u v) :=
  α → β

#check Arrow Nat Bool        -- Nat → Bool : Type
#check Arrow (List Nat) Nat    -- (Type 0) → Nat : Type 1


def Compose2.{u, v, w}
    (F : Type v → Type w) (G : Type u → Type v) : Type u → Type w :=
  fun α => F (G α)

#check Compose2 Option List Nat  -- Option (List Nat)
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

