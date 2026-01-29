
A Tour of L∃∀N
===

About Lean
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

Installing Lean
===

The easiest way to install Lean is to follow the quickstart guide at
- [Lean Quickstart](https://lean-lang.org/lean4/doc/quickstart.html)

You will need first install VS Code:

- [VS Code](https://code.visualstudio.com/)

Then go to `View > Extensions` and search for "Lean 4" and install it.

This will put a `∀` in the upper right menu bar of VS Code. From there, you can
create a new project, which should install Lean and all of the associated tools.

Lean "Project" Types
===

With the VS Code Extension, you can install two types of projects:

- **Standalone** project. Just the basics.

- **Mathlib** project. Includes a *huge* library of most basic and several advanced areas of mathematics.
Choose this if in particular if you want to use real numbers, algebra, sets, matrices, etc.

Despite its size, I recommend starting a *Mathlib* based project. You never know
when you might need something from Mathlib.

Notes:
  - Wait for the tool to completely finish before opening or changing anything.
  - I don't like the option where it creates a new workspace.
  - Don't make a new project every time you want to try something out.
      - Each project is about 6GB to start with
      - Instead, create a single monolithic project and make sub-directories for ideas you want to explore.

Directory Structure
===

If you create a new project called `EE598_Turing`, you will get a whole directory of stuff:

```
   EE598_Turing
     .github/
     .lake/
     EE598_Turing/                 <-- put your code here
       Basic.lean
       HW_I_2.lean                 <-- Today's HW file
     .gitignore
     EE598_Turing.lean
     lake-manifest.json
     lakefile.toml
     lean-toolchain
     README.md
```

For now, you mainly need to know that the subdirectory with the same name as your
project is where you can put your `.lean files`. It has one in it already, called `Basic.lean`.
Open this and you can start playing with Lean.

Exercises
===

<ex/> Create a Mathlib-based project using `EE598_Lastname` as the project name.
E.g, if your last name is Turing, name your project `EE598_Turing`.

<ex/> Create a new file `HW_I_2.lean` so that it has the code:


```lean
import Mathlib.Tactic.Linarith

#eval 1+2

example (x y z : ℚ)
        (h1 : 2*x < 3*y)
        (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  grind
```


Open the Lean Infoview (`∀` menu) and check the results.

**Note:** If you do `import Mathlib`, VS Code will launch a process to compile *everything* in
Mathlib, which can take an hour or so. At some point this week, do this so that you don't
constantly need to hunt for the exact `Mathlib` directory you need.

Course Notes
===

The course notes I am presenting are on under construction Github at
> [https://github.com/klavins/LeanW26](https://github.com/klavins/LeanW26)

The source code for every slide deck is in an executable `.lean` file.

Feel free to clone this repo as well, but note I will make updates constantly. So periodically do

```bash
git update
```

to make sure you have the latest version.

Fancy Characters
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


Exercises
===

<ex/> Figure out how to encode this statement:

&nbsp; &nbsp;  &nbsp;  &nbsp; $\mathtt{theorem} \;\mathtt{T}_1 \; : \; \forall \; \mathtt{x} : \mathbb{R}, \; \mathtt{0} \leq \mathtt{x}$ ^ $2 := \mathtt{sorry}$



Type Checking
===

L∃∀N is based on type theory. This means that every term has a very well-defined type.
To find the type of an expression, use #check. The result will show up in the Infoview.  
```lean
#check 1
#check "1"
#check ∃ (x : Nat), x < 0
#check fun x => x+1
```

Exercises
===

<ex/> Use `#check` to determine the types of `(4,5)`, `ℕ × ℕ`, and `Type`.

Evaluation
===

You can use Lean to evaluate expressions using the `#eval` command. The result
will show up in the Infoview. 
```lean
#eval 1+1
#eval "hello".append " world"
#eval if 2 > 2 then "the universe has a problem" else "everything is ok"
#eval Nat.Prime 1013
```

Proofs
===

We will go into proofs in great detail later. For now, know that you can
state theorems using the `theorem` keyword. 
```lean
theorem my_amazing_result (p : Prop) : p → p :=
  fun h => h
```
 In this expression,

```text
  my_amazing_result is the name of the theorem
  (p : Prop)        is an assumption that p is a true or false statement
  p → p             is the actual theorem
  :=                delineates the theorem from the proof
  λ h => h          (the identity function) is the proof
```

You can use your theorems to prove other theorems: 
```lean
theorem a_less_amazing_result : True → True := by
  apply my_amazing_result
```

Examples vs Proofs
===

Results don't have to be named, which is useful for trying things
out or when you don't need the result again. 
```lean
example (p : Prop) : p → p :=
  fun h => h

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) :=
  fun ⟨ hpq, hqr ⟩ hp
    => hqr (hpq hp)
```

The Tactic Language and `sorry`
===

The examples above use fairly low level Lean expressions to prove statements.
Lean provides a higher level DSL (domain specific language) for proving.
You enter the Tactic DSL using `by`. 
```lean
example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  sorry
```
 which can be built up part by part into 
```lean
example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  intro ⟨ hpq, hqr ⟩
  intro hp
  have hq : q := hpq hp
  have hr : r := hqr hq
  exact hr
```
 Don't worry if none of this makes sense. We'll go into all the gory details later.

Exercises
===

<ex /> Lean provides a powerful tactic called `aesop`. Redo the proof
of the previous example replacing the proof with the single line `aesop`.


Programming
===

L∃∀N is a full-fledged functional programming language. Much of
L∃∀N is programmed in L∃∀N (and then compiled).

If you are not familiar with functional programming: you will be by then end of this course.

Here is an example program: 
```lean
def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => if x = 0 then remove_zeros Q else x::(remove_zeros Q)

#check remove_zeros

#eval remove_zeros [1,2,3,0,5,0,0]     -- [1,2,3,5]
```
 Note the similarity between `def` and `theorem`. The latter is
simply a special kind of definition. 

Exercises
===

<ex /> Write a function `square` that squares every number in a list
of natural numbers. Use `remove_zeros` as a template. Test your
code using `#eval`.



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
 </a> — Google for L∃∀N, also in VS Code

- <a href="https://leanprover.zulipchat.com/" target="other">
  Zulip Chat
  </a> — Discussion groups


Exercises
===

<ex /> Go to Loogle and look up `List.find?`. There should be two examples
of how to use this function. Try them in your `HW_I_2.lean` file.

Homework Routine
===

Each slide deck contains
- Warm up exercises interspersed with the slides, mostly done in class
- A final set of exercises that should be done on your own

When we finish a slide deck, **all** solutions should be put
into a file with the same name in your project directory. This
is primarily a way to backup your code.

To turn in a solution set, submit a standalone file to Canvas.

I will download all solution sets into a Lean project and
execute your code to grade them.

Late homework accrues 10% reduction per week.


Exercises
===

<ex/> If you have not done so already, create a file called `HW_I_2.lean`
in the same directory as `Basic.lean`.
Put your solutions to the exercises in this slide deck in this file.
- Homework files should restate each problem.
- Textual answers should be written as comments.
- Lean code should be executable assuming Mathlib is installed and
should produce no errors.
- If you are stuck on part of a theorem, use `sorry` for
partial credit and move on with your life.

<ex/> Make a github repo for your homework using the same as your project
(e.g. `EE598_Turing`). You will use this repo to save your homework. Make the repo `private`.

<ex/> Once you are satisfied with your work, submit the `HW_I_2.lean` file
to Canvas under the corresponding assignment.



License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

