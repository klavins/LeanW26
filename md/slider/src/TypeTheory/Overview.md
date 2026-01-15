
Foundations of Mathematics
===

Overview
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
- E.g. The [Continuum Hypothesis](https://arxiv.org/abs/2102.02901) is neither provable nor unprovable from the axioms of set theory.

**Uncomputability (Turing, 1936) (Church, 1936)**
- Some problems are uncomputable: No algorithm exists to decide all possible instances

**Takeaways**
- All mathematical results are relative to a set of axioms
- Automated mathematics tends to be conservative, and constructive


Zermelo Fraenkel Set Theory
===

**Axioms**
- Extensionality – Sets with the same elements are equal.
- Empty Set – There exists a set with no elements.
- Pairing – For any two sets, there is a set containing exactly those two sets.
- Union – For any set of sets, there is a set containing all their elements.
- Power Set – For any set, there is a set of all its subsets.
- Infinity – There exists an infinite set
- Separation – Subsets can be formed by properties that refer to existing sets
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
    - Arithmetic, Analysis, Topology, have all been constructed within ZF

Proof Assistants
- *Mizar* uses a version of ZFC
- *Isabelle/ZF* uses ZF, but most people use *Isabelle/HOL*
- *Lean/Mathlib's* `Set` is consistent with ZF


Problems with ZF
===

- You can write `x ∈ x` and have to prove it does not follow from the axioms
- It is not *constructive*, thus hard to encode algorithmically
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
- Type universes, with `Prop` as the sole impredicative Type
- Inductive Types
- Definitional Equality
- Type checking and inference
- Quotients

Additionally:
- Type classes (organizational but powerful)
- A sophisticated elaborator / syntax creator
- Easy to extend to classical logic
- Supports meta-programming _in Lean_.

<div class='fn'>An <it>impredicative</it> type can quantify over
types in its own universe, including itself. This is allowed in
<tt>Prop</tt> because <tt>Prop</tt> values (i.e. proofs) are
erased in computation. So you can't use them in computations
to yield a paradox.
</div>



Beyond CIC
===

Lean's Type Theory (CIC+quotients) does not have native support for:

- **Higher inductive types**. Inductive types describe how to define
single elements of a given type. HITs also describe how to define
equality for the type, and equality of equality, etc.

- **Univalence**: Isomorphic structures are not equal, making many natural
arguments overly complicated. For example, `Empty ⊕ A ≅ A`, but that does
not mean they are equal.

- **Coinduction**: Coinductive definitions, resulting in infinite
objects, are in general not allowed. Although Lean 4.25.0 added support for
[coinductive predicates](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/).



Exercises
===

<ex/> (Advanced, Optional) Mathlib defines sets as

```lean
def Set.{u} (α : Type u) : Type u := α → Prop
```
Show that this definition is consistent with the axioms of ZF.



λ-Calculus
===

The **λ-calculus** was introduced in the 1930s by Alonzo Church as a way
to represent functions and how they are calculated using symbols.

Church asked: Is there an algorithm to decide any mathematical question?

Church showed that the answer is "no". The reasoning, roughly, is this:

  - Devise a simple programming language, the λ-calculus
  - Define computation as rewriting operations on λ-calculus terms
  - The set of algorithms (λ-calculus expressions) is countable, but
  the set of total functions is not. So there exist functions without
  algorithms.

<div class='fn'>For example, there is no algorithm that decides whether
a λ-calculus term normalizes.</div>

Syntax and Reduction
===

Specifically, the λ-calculus has two parts:

**Term Syntax**
- Variables: `x, y, z, ...` are terms
- Abstraction: If `x` is a variable and `M` is a term then `λ x ↦ M` is a term
- Application: If `M` and `N` are terms, then `M N` is a term

**β-Reduction**
- `λ x ↦ M` applied to `N` is `M[N/x]`, where all occurrences of x are replaced with N.

λ-Calculus in Lean
===

In Lean you can write lambda calculus statements and reduce them, for example:


```lean
def f1 := λ x ↦ x+1
def g1 := λ x ↦ λ y ↦ 2*x-y

#reduce f1 2         -- 3
#reduce g1 2 3       -- 1
```
 Note: The Lean Powers have recently decreed that `λ` and `↦` should be written as `fun` and `=>`.
So, we'll use syntax like: 
```lean
def f2 := fun x => x+1
def g2 := fun x y => 2*x-y
```

Exercises
===

<ex/> Define a lambda called `h` that returns the square of its argument.

<ex/> Evaluate `h (h (h 2))`.




Unsolvable Problems
===

A specific problem that Church showed to be unsolvable is:

> Given λ-calculus terms M and N, show there does not exist a λ-calculus function
that can determine whether M can be rewritten as N.

This argument is similar to Alan Turing's similar result which shows there is no
Turing Machine that can determine whether a given Turing Machine eventually terminates.

The *Church-Turing Thesis* is the observation that _all_ formalizations of
computation are equivalent to the λ-calculus or, equivalently, Turing Machines.

The former is more convenient for symbolic reasoning, while the latter is more
akin to how electromechanical computers actually work.

Programming Languages
===

Thus, the λ-calclus and the formal notion of computation has its roots in the
foundations of mathematics.

In the 1960s, linguists and computer scientists realized that the λ-calculus
was a useful framework for the theory and design of programming languages.

Logicians were also exploring exploring Type Theory as an alternative.
In 1980s many of these ideas came together, especially through the work of
Thierry Coquand on the *Calculus of Constructions*.

Eventually typed programming languages emerged as an alternative foundation
for all of mathematics and they could be used to develop computational proof assistants
and theorem provers such as Coq, NuPRL, and HOL.


Infinite Loops
===

Central to Church's (and Turing's) argument is that some evaluations go on infinitely,
some do not, and it is not always easy to tell the difference.

Here is an easy example of infinite behavior. Define
```
Ω := λ x => x x
```
Consider `Ω` applied to itself `Ω`:
```
(λ x => x x) (λ x => x x)       —β—>       (λ x => x x) (λ x => x x)
```
producing an infinite loop.

Exercises
===

<ex/> Define `Ω` in Lean and explain what happens.


Curry's Paradox
===

Infinite Loops made the λ-calculus expressive enough for Church
to prove his undecidability results, but it caused other problems.

Haskel Curry discovered that one could encode the following paradox in logical
systems built from the λ-calculus.

  - Suppose X = X → Y where Y is _any_ statement.
  - Certainly X → X is true for any statement X.
  - Substituting X → Y for the second X gives X → (X → Y)
  - This statement is equivalent to X → Y, which is X by assumption.
  - Thus X is true
  - So Y is true since X → Y

For example, X → Y could mean "If this sentence is true, then 1 < 0."

Types
===

The solution was to assign _types_ to all terms in the λ-calculus.
- Self referential programs are impossible to assign types to.
- Infinite loops are no longer allowed (less powerful computationally).

Thus was born the _simply-typed λ-calculus_.

Eventually, more complicated types were added, in which type definitions could
depend on other types or on even terms.

Most modern programming languages and some logical frameworks have these properties.

The Simply-Typed Lambda Calculus
===

In the expressions we wrote above, the types were inferred, but we can write them out.

```lean
def f3 : Nat → Nat := fun (x : Nat) => x+1
def g3 : Nat → Nat → Nat := fun (x y : Nat) => 2*x-y
```

However, `Nat` is not a *simple* type (it is an *inductive* type).

In the next section we'll look at what exactly is `Type` and come back to
the lambda calculus in the following section.


Exercise
===

<ex /> Watch this video (https://www.youtube.com/watch?v=iM_0Rxqqn7Y) on Lean and come up with
three questions you would like to ask this speaker. For each question, see how much you can
answer by doing some research and reading to refine the question.


```lean
--hide
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

