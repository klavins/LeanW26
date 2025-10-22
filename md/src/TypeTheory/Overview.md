
Foundations of Mathematics
===

**Goal**: A small set of axioms from which all of mathematics can be derived.

**Should explain:**
- What is a number (natural, integer, real, complex, ...)
- What is a logical statement
- What is a proof
- Etc.

**Should be**:
- Sound (everything provable from the axioms is actually true)

**Should Avoid:**
- Paradoxes (e.g. does the set of all sets contain itself?)

Cracks in the Edifice of Mathematics
===

**Russell's Paradox (1901)**
- Define R = { x | x ∉ x }
- Is R ∈ R? If yes, then R ∉ R. If no, then R ∈ R.

**Gödel’s Incompleteness Theorem (1930)**
- Any sufficiently expressive formal system is incomplete
- E.g. The *Continuum Hypothesis* is neither provable nor unprovable from the axioms of set theory.

**Uncomputability (Turning, 1936, numbers) (Church, 1936, Logic)**
- Some problems are uncomputable: No algorithm exists to decide all possible instances

**Take-aways**
- All mathematical results are relative to a set of axioms
- Automated mathematics tends to be conservative, and constructive


Zermelo Fraenkel Set Theory
===

ZFC is a one-sorted theory in first-order logic.

**Axioms**
- Extensionality – Sets with the same elements are equal.
- Empty Set – There exists a set with no elements.
- Pairing – For any two sets, there is a set containing exactly those two sets.
- Union – For any set of sets, there is a set containing all their elements.
- Power Set – For any set, there is a set of all its subsets.
- Infinity – There exists an infinite set
- Separation – Subsets can be formed by properties
- Replacement – Images of sets under definable functions are sets.
- Foundation – No infinite descending inclusion-chains (x₀ ∋ x₁ ∋ x₂ ∋ ...)

**Optional**
- Axiom of Choice (ZFC = ZF + AC)

Building Math from Sets
===

- Natural Numbers:
    - 0 := ∅, 1 := {∅}, 2  := {∅,{∅}}, …
- Ordered pairs:
    - (a,b) := {{a},{a,b}}
- Functions and relations:
    - Sets of ordered pairs
- Etc.
    - Arithmetic, Analysis, Topology, can all be constructed within ZF

Proof Assistants
- *Mizar* uses a version of ZFC
- *Isabelle/ZF* uses ZF, but most people use *Isabelle/HOL*
- *Lean/Mathlib's* `Set` is consistent with ZF


Problems with ZF
===

- You can write x ∈ x and have to prove it does not follow from the axioms
- Proofs exist outside of ZF
- It is not *constructive*, so hard to encode algorithmically
- Not amenable to computation (no data structures, not modular, ...)


Type Theory
===

Introduced as a foundation for computation and reasoning, and eventually
served as the basis of proof assistants like Coq, Rocq, Agda, Lean, and others.
- Alonzo Church : The simply typed λ-Calculus (1940)
- Per Martin-Löf : Intuitionistic type theory (1972)
- Thierry Coqrand : Calculus of Constructions and Coq (1988)

The Curry Howard Isomorphism Says
- Logical Statements are Types
- Proofs are programs

There are many flavors of type type theory: Simple, Dependent, Homotopy, Cubical

Some are easy to automate, and some are not.


Lean's Type Theory
===

The *Calculus of Inductive Constructions*
- Typed Lambda Calculus / Arrow Types
- Dependent types
- Type universes, with `Prop` as an impredicative Type
- Inductive Types
- Definitional Equality
- Type checking and inference
- Quotients

Additionally:
- Type classes (organizational but powerful)
- A sophisticaed elaborator / syntax creator
- Easy extend to classical logic



Beyond CIC
===

Lean's Type Theory does not have native support for:
- **Higher inductive types**. For example, defining homotopy is clunkiny in Lean.
- **Univalence**: Isomorphic structures are not equal, making many natural arguments clunky.
- **Coinduction**: Coinductive definitions that result in infinite objects are not allowed.


Exercises
===

1. (Advanced) Mathlib defines sets as

```lean
def Set.{u} (α : Type u) : Type u := α → Prop
```
Show that this definition is consistent with the axioms of ZF.

2. (Advanced) Consider

```lean
inductive MyStream (A : Type) : Type where
| Cons : A → MyStream A → MyStream A

def ones : MyStream Nat := MyStream.Cons 1 ones
```

Explain why Lean gives the error: `failed to show termination` and
devise a workaround that enables some kind of coinductive reasoning.



License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

