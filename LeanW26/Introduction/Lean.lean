--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

/-
A Tour of L∃∀N 4
===

L∃∀N is a programming language and proof assistant.

It is an implementation of the *Calculus of Inductive Constructions*, a type
theoretic foundation for mathematics.

You can use it to
- state almost any mathematical definition or theorem
- write formal proofs of your theorems
- check that your proofs are correct

While L∃∀N will not prove all of your theorems for you, it does provide an increasing amount of
automation making it easier than ever to use a proof assistant.

Installing L∃∀N
===

The easiest way to install L∃∀N is to follow the quickstart guide at
- [Lean Quickstart](https://lean-lang.org/lean4/doc/quickstart.html)

You will need first install VS Code:

- [VS Code](https://code.visualstudio.com/)

Then go to `View > Extensions` and search for "Lean 4" and install it.

This will put a `∀` in the upper right menu bar of VS Code. From there, you can
create a new project, which should install Lean and all of the associated tools.

L∃∀N "Project" Types
===

With the VS Code Extension, you can install two types of projects:

- **Standalone** project. Just the basics.

- **Mathlib** project. Includes a *huge* library of most basic and several advanced
areas of mathematics. Choose this if in particular if you want to use real numbers,
algebra, sets, matrices, etc.

Despite its size, I recommend starting a *Mathlib* based project. You never know
when you might need something from Mathlib.

Notes:
  - Wait for the tool to completely finish before opening or changing anything.
  - I don't like the option where it creates a new workspace
  - Don't make a new project every time you want to try something out. You will use
  up all the space on your hard drive. Instead, create a single monolithic project
  and make subdirectores for ideas you want to explore.

Directory Structure
===

If you create a new project called `EE598_Turing`, you will get a whole directory of stuff:

```
   EE598_Turing
     .github/
     .lake/
     MyProject/                    <-- put your code here
       Basic.lean
     .gitignore
     EE598_Turing.lean
     lake-manifest.json
     lakefile.toml
     lean-toolchain
     README.md
```

For now, you mainly need to know that the subdirectory with the same name as your
project is where you can put your .lean files. It has one in it already, called `Basic.lean`.
Open this and you can start playing with Lean.

Exercise 1 : Make a Project
===

a. Create a Mathlib-based project using `EE598_Lastname` as the project name.
E.g, if your last name is Turing, name your project `EE598_Turing`.

b. Edit the file `Basic.lean` so that it has the code -/

import Mathlib.Tactic.Linarith

#eval 1+2

example (x y z : ℚ)
        (h1 : 2*x < 3*y)
        (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith

/-

Make sure it works.

Exercise 2: Fancy Characters
===

You can enter fancy characters in Lean using escape sequences

```
  →                   \to
  ↔                   \iff
  ∀                   \forall
  ∃                   \exists
  ℕ                   \N
  xᵢ                  x\_i
```

Go to `∀ > Documentation > ... Unicode ...` for a complete list.

**TODO** Figure out how to encode this statement: -/

theorem T₁ : ∀ x : ℝ, 0 ≤ x^2 := by
  apply sq_nonneg

/-

Exercise 3: Type Checking
===

L∃∀N is based on type theory. This means that every term has a very well defined type.
To find the type of an expression, use #check. The result will show up in the Infoview.  -/

#check 1
#check "1"
#check ∃ (x : Nat) , x > 0
#check fun x => x+1
#check (4,5)
#check ℕ × ℕ
#check Type

/-
**TODO**: What is are the types of (4,5), ℕ × ℕ, and Type?

Evaluation
===

You can use Lean to evaluate expressions using the `#eval` command. The result
will show up in the Infoview. -/

#eval 1+1
#eval "hello".append " world"
#eval if 2 > 2 then "the universe has a problem" else "everything is ok"
#eval Nat.Prime 741013183

/-
Proofs
===

We will go into proofs in great detail next week. For now, know that you can
state theorems using the `theorem` keyword. -/

theorem my_amazing_result (p : Prop) : p → p :=
  fun h => h

/- In this expression,

  my_amazing_result is the name of the theorem
  (p : Prop)        is an assumption that p is a proposition
                    (true or false statement)
  p → p             is the actual theory
  :=                delinates the statement of the theorem
                    from the proof
  λ h => h          (the identity function) is the proof

You can use your theorems to prove other theorems: -/

theorem a_less_amazing_result : True → True :=
  my_amazing_result True

/-
Examples vs Proofs
===

Results don't have to be named, which is useful for trying things out or when you don't
need the result again. -/

example (p : Prop) : p → p :=
  fun h => h

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) :=
  fun ⟨ hpq, hqr ⟩ hp => hqr (hpq hp)


/-
The Tactic Language and `sorry`
===

The examples above use fairly low level Lean expressions to prove statements. Lean
provides a very powerful, higher level DSL (domain specific language) for proving.
You enter the Tactic DSL using `by`.

Proving results uses the super `sorry` keyword. Here is an example of Tactics and sorry. -/

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  sorry

/- which can be built up part by part into -/

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  intro ⟨ hpq, hqr ⟩
  intro hp
  have hq : q := hpq hp
  have hr : r := hqr hq
  exact hr

/- Don't worry if none of this makes sense. We'll go into all the gory details later.

Programming
===

L∃∀N is also a full-fledged functional programming language. For example, much of
L∃∀N is programmed in L∃∀N (and then compiled). That said, the L∃∀N Programming
Language is not really general purpose: You would probably lose your mind trying
to build an operating system with L∃∀N. Rather, L∃∀N is a programming language
designed first for programming L∃∀N itself, and second for build mathematical
data structures and algorithms.

If you are not familiar with functional programming: you will be by then end of this course.

Here is an example program: -/

def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => if x = 0 then remove_zeros Q else x::(remove_zeros Q)

#check remove_zeros

#eval remove_zeros [1,2,3,0,5,0,0]

/- Note the similarity between `def` and `theorem`. The latter is simply a special
kind of definition.

Documentation and Resources
===

- <a href="https://lean-lang.org/theorem_proving_in_lean4/" target="other">
  Theorem Proving in Lean
  </a>

- <a href="https://lean-lang.org/functional_programming_in_lean/" target="other">
  L∃∀N Programming Book
  </a>

- <a href="https://leanprover-community.github.io/lean4-metaprogramming-book/" target="other">
  L∃∀N Metaprogramming
  </a>

- <a href="https://leanprover-community.github.io/mathematics_in_lean" target="other">
  Mathematics in L∃∀N
  </a>

- <a href="https://github.com/leanprover/lean4/blob/ffac974dba799956a97d63ffcb13a774f700149c/src/Init/Prelude.lean" target="other">
  The Standard Library
  </a>

- <a href="https://loogle.lean-lang.org/" target="other">
 Loogle
 </a> — Google for L∃∀N

- <a href="https://leanprover.zulipchat.com/" target="other">
  Zulip Chat
  </a> — Discussion groups



Exercise 4 : Homework and Github
===

a. Create a file called `HW1.lean` in the same directory as `Basic.lean`.

b. Make a github repo for you project using the same name. You will use this
repo to turn in your homework. Make the repo `private` and share it with
`klavins` so I can access it. I will do

```bash
git clone https://github.com/turing/EE546_Turing.git
```

supposing your git username is `turing` to get your code. I will pull subsequent
changes using:

```bash
git pull origin master
```

from within that directory. Homework files should restate each problem
(just copy and paste the problem statement. Textual answers should be written
as comments. Lean code should be executable assuming Mathlib is installed and
produce no errors. If you are stuck on part of a theorem, use `sorry` for
partial credit.

c. Email `klavins@uw.edu` with a link to your repository.

-/
