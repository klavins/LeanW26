--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26



/-
Curry-Howard Isomorphism
===
-/

/-

Intuition
===

Consider the types:
```
A → A
(C → A) → C → A
```

The first is the type of a function on `A`. The second is the type of a
function that takes a function on `C → A`.

We can read these as propositional formulas stating
```
A implies A
(C implies A) implies C implies A
```

The **Curry-Howard Isomorphism** emerges from the observation that the λ expressions
having the above types act like proofs that the above implications are tautologies!

With this observation, the statement x : A reads "x is a proof of A". Furthermore,
```
λ x : A => x
```

is a method that takes a proof of `A` and returns a proof of `A`, proving the implication `A → A`.




Types ≡ Propositions
===

To state the CHI exacly, we will restrict ourselves to showing that Propositional Logic with only
implication (→) is isomorphic to the simply typed λ-calculus. We will need one definition.

**Def:** Given a context Γ = { x₁: φ₁, x₂ : φ₂, ..., xₙ : φₙ }, the _range_ of Γ,
denoted |Γ|, is { φ₁, φ₂, ..., φₙ }.

**Theorem:** If Γ ⊢ M : φ then |Γ| ⊢ φ.

**Proof Sketch:** We convert any type derivation tree into a propositional proof by replacing
VAR with AX, ABST with →-Intro, and APPL with →-Elim. This is done by induction on the proof tree.
Here we just show an example which should be easily generalized. The type proof tree in the
slide deck on type inference can be re-written be removing all "x : " and renaming the rules.
```none
    ————————————————————— AX       ———————————————————— AX
     C → A, C  ⊢  C → A               C → A, C  ⊢  C
  ——————————————————————————————————————————————————————————— →Elim
                      C → A, C   ⊢  A
                    ——————————————————— →-Intro
                      C → A  ⊢  C → A
                   —————————————————————— →-Intro
                    ⊢  (C → A) → C → A
```

Curry-Howard: Propositions → Types
===

The opposite direction of the CHI is more technical. We have to show how to produce a
λ-calculus term M from aproof of `φ` so that `M : φ`. For example, suppose we started
with the propositional proof tree in the previous section. How would we produce the
type derivation from it? Here we will outline how this is done in general.

First we need a way to produce a type context from a propositional context. Suppose that
```
Γ = { φ₁, φ₂, ..., φₙ }
```

and define
```
Δ = { x₁ : φ₁, x₂ : φ₂, ..., xₙ : φₙ }
```

where the `xᵢ` are introduced as new type variables. The object `Δ` is a simple function of `Γ`.

**Theorem:** If `Γ ⊢ φ` then there exists a λ-calculus term `M` such that `∆ ⊢ M : φ`.

The proof uses induction on the proof tree that shows `Γ ⊢ φ`.
Since there are three rules (AX, →Intro, and →-Elim), we have three cases,
which we handle one by one.


Proof : Case 1
===

**Case:** The proof ends with `Γ,φ ⊢ φ` by the VAR rule

**Subcase 1**: If `φ ∈ Γ` then there is some type variable `x` such that `x : φ ∈ Δ`.
By the VAR rule we can conclude
```
Δ  ⊢  x : φ
```

**Subcase 2**: If `φ ∉ Γ` then we introduce a new variable `x` such that `x : φ`.
Once again by the VAR rule
```
Δ, x : φ  ⊢  x : φ
```

Why do we need two sub-cases? It's because of how we defined `Δ` on the previous
as related to `Γ` and not to `Γ ∪ { x : φ }`)

Proof : Case 2
===

**Case:** The proof ends with →Elim

Suppose the proof that `Γ ⊢ φ` ends with
```none
    Γ ⊢ ρ → φ      Γ ⊢ ρ
  ——————————————————————————
           Γ ⊢ φ
```
We need to find a λ-term that has type `φ`. Here the premises of the above rule
instance allow us to assume the induction hypothesis that there exists `M` and `N` such that
```
Δ ⊢ M : ρ → φ
Δ ⊢ N : ρ
```
By the ABST rule, we can conclude
```
Δ ⊢ M N : φ
```

Proof : Case 3
===

**Case:**: The proof ends with →Intro

Suppose the proposition `φ` has the form the `ρ → ψ` and the proof `Γ ⊢ ρ → ψ` ends with
```
     Γ, ρ ⊢ ψ
  ——————————————
    Γ ⊢ ρ → ψ
```

**Subcase 1**: `ψ ∈ Γ`. By the induction hypothesis, there is a term `M` such that `Δ ⊢ M : ψ`.
Introduce a variable `x` (not used in `Δ`) such that `x : ρ`. Then we can conclude
```
Δ, x : ρ  ⊢  M : ψ
```

and by the ABST rule
```
Δ ⊢ λ x : ρ => M : ρ →  ψ
```

**Subcase 2**: `ψ ∉ Γ`. Then by the induction hypothesis, there is a term `M` such that
```
Δ, x : ρ ⊢ M : ψ
```

from which we may also conclude
```
Δ ⊢ λ x : ρ => M : ρ →  ψ
```
-/


/-
Propositions, Theorems, and Proofs in Lean
===

The Curry-Howard approach is exactly how proofs of theorems are done in Lean.
We show that the proposition to be proved is inhabited. In the examples below,
we use the type `Prop`, from Lean's standard library.

We will start by declaring two variables of type Prop. We use curly braces here
instead of parentheses for reasons we will explain later. -/

variable {A C : Prop}

/- To prove a proposition like`A → A`, we define the identity function from `A` into `A`,
showing the proposition considered as a type is occupied. -/
def my_theorem : A → A :=
  fun proof_of_A : A => proof_of_A

/- We have called the bound variable in the lambda expression `proof`, but you could call the bound
variable anything you like. A common scheme is to refer to a proof of `x` by `hx`. -/

def my_theorem' : A → A :=
  fun hA : A => hA


/-
Applying Theorems to Prove Other Theorems
===

Lean provides the keyword `theorem` for definitions intended to be results, which is like `def`
but requires the type of the function being defined to be `Prop`.

As another example, we prove the other proposition we encountered above.
Here we call the bound variables pca for "proof of c → a" and pc for "proof of c".  -/

theorem another_theorem : (C → A) → C → A :=
  fun hca : C → A =>
  fun hc : C =>
  hca hc

/- Or we can use our first theorem to prove the second theorem. Notice
how `my_theorem` acts as a function from proofs to proofs. -/

theorem another_theorem_v2 : (C → A) → C → A :=
  fun h : C → A => my_theorem h

/-
Another Example
===
-/

theorem t1 : A → C → A :=
  fun ha : A =>
  fun hc : C =>                                -- Notice that hc is not used
  ha

theorem t2 : A → C → A :=
  fun ha hc  => ha                             -- We can use fun with two arguments

theorem t3 : A → C → A :=
  fun ha _ => ha                               -- We can tell Lean we know hc is not used

example : A → C → A :=                         -- We can state and prove an unnamed theorem
  fun ha _ => ha                               -- using the `example` keyword

/-
Note that the `example` keyword does not require its type
to be `Prop`. For example:
-/

example : ℕ := 1

/- Whereas `theorem` does require its type to be `Prop`. -/


/-
Negation
===

`False` is defined inductively as
```lean
inductive False where
```
That is, there are no terms of type False. -/

--hide
variable (p q : Prop)
--unhide

example : False → p :=
  fun hf => nomatch hf     -- there is no work to do because there is
                           -- nothing to match.

/-
In type theory, *a match with no cases may have any type*.

To use this pattern, recall that `¬p` is the same as `p → False`
(a function type).
-/

example : p → ¬p → q :=
  fun ha =>                        -- ha : p
  fun hna =>                       -- hna : (p → False)
  nomatch hna ha                   -- hna ha = False

example : (p → q) → (¬q → ¬p) :=
  fun hpq nq hp => nomatch nq (hpq hp)



/-

We will show how all the other connectives work in the next slide deck.

Variable Declarations
===

If we write
-/

def thm1 (A : Prop) : A → A :=
  fun h : A => h

/- vs -/

def thm2 {A : Prop} : A → A :=
  fun h : A => h

/- We get the same theorem. But in the latter we are asking Lean to infer the type, which is
usually more convenient. For example: -/

example : (p → q) → (p → q) :=
  fun hpq => thm1 (p → q) hpq

/- vs -/

example : (p → q) → (p → q) :=
  fun hpq => thm2 hpq           -- Lean infers A is p → q

/-
Exercises
===

<ex /> Prove the following using only lambda expressions and (possibly) `nomatch`.

-/

variable (P Q : Prop)

example : P → P → P → P := sorry
example : (P → Q) → (¬Q → ¬P) := sorry
example : ¬p → (p → q) := sorry
example : (∀ x, x > 0) → (∀ y, y > 0) := sorry

/-
References
===

Morten Heine Sørensen, Pawel Urzyczyn
"Lectures on the Curry-Howard Isomorphism"
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
  - Chapter 4 describes Intuitionistic Propositional Logic

-/



--hide
end LeanW26
--unhide
