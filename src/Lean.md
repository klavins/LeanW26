
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Lean.lean'>Code</a> for this chapter</span>
 # A Tour of Lean 4

## Installing Lean

The easiest way to install Lean is to follow the quickstart guide at
- [Lean Quickstart](https://lean-lang.org/lean4/doc/quickstart.html)

You will need first install VS Code:

- [VS Code](https://code.visualstudio.com/)

Then go to `View > Extensions` and search for "Lean 4" and install it.

This will put a `∀` in the upper right menu bar of VS Code. From there, you can create a new project, which should install Lean and all of the associated tools.

## Lean "Project" Types

With the VS Code Extension, you can install two types of projects:

- **Standalone** project. Just the basics.

- **Mathlib** project. Includes a *huge* library of most basic and several advanced areas of mathematics. Choose this if in particular if you want to use real numbers, algebra, sets, matrices, etc.

Despite its size, I recommend starting a *Mathlib* based project. You never know when you might need something from Mathlib.

Notes:
  - Wait for the tool to completely finish before opening or changing anything.
  - I don't like the option where it creates a new workspace
  - Don't make a new project every time you want to try something out. You will use up all the space on your hard drive. Instead, create a single monolithic project and mkae subdirectores for ideas you want to explore.

## Directory Structure

If you create a new project called `MyProject`, you will get a whole directory of stuff:

```
   MyProject
     .github/
     .lake/
     MyProject/                    <-- put your code here
       Basic.lean
     .gitignore
     MyProject.lean
     lake-manifest.json
     lakefile.toml
     lean-toolchain
     README.md
```

For now, you mainly need to know that the subdirectory with the same name as your project is where you can put your .lean files. It has one in it already, called `Basic.lean`. Open this and you can start playing with Lean.

## Testing an Installation

Try replacing the code in `Basic.lean` with the following: 
```lean
import Mathlib.Tactic.Linarith

#eval 1+2

example (x y z : ℚ)
        (h1 : 2*x < 3*y)
        (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0) : False := by
  linarith
```
 If it is not open already, open `Lean infoview` via the ∀ menu.

- Put your curor over `1+2`. You should see 3 in the messages.
- Put your cursor just before `by` you will get some goals.
- Rut it after `linarith` you will see "No Goals", since the theorem is proved.

## Fancy Characters

You can enter fancy characters in Lean using escape sequences

```
  →                   \to
  ↔                   \iff
  ∀                   \forall
  ∃                   \exists
  ℕ                   \N
  xᵢ                  x\_i
```

Go to

```
  ∀ > Documentation > ... Unicode ...
```

for a complete list.

## Type Checking

Lean is based on type theory. This means that every term has a very well defined type. To find the type of an expression, use #check. The result will show up in the Infoview.  
```lean
#check 1
#check "1"
#check ∃ (x : Nat) , x > 0
#check λ x => x+1
#check (4,5)
#check ℕ × ℕ
#check Type
```
 ## Evaluation

You can use Lean to evaluate expressions using the #eval command. The result will show up in the Infoview. 
```lean
#eval 1+1
#eval "hello".append " world"
#eval if 2 > 2 then "the universe has a problem" else "everything is ok"
#eval Nat.Prime 741013183
```
 ## Proofs

We will go into proofs in great detail next week. For now, know that you can state theorems using the `theorem` keyword. 
```lean
theorem my_amazing_result (p : Prop) : p → p :=
  λ h => h
```
 In this expression,

  my_amazing_result is the name of the theorem
  (p : Prop)        is an assumption that p is a proposition
                    (true or false statement)
  p → p             is the actual theory
  :=                delinates the statement of the theorem
                    from the proof
  λ h => h          (the identity function) is the proof

You can use your theorems to prove other theorems: 
```lean
theorem a_less_amazing_result : True → True :=
  my_amazing_result True
```
 ## Examples vs Proofs

Results don't have to be named, which is useful for trying things out or when you don't need the result again. 
```lean
example (p : Prop) : p → p :=
  λ h => h

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) :=
  λ ⟨ hpq, hqr ⟩ hp => hqr (hpq hp)
```
 ## The Tactic Language and `sorry`

The examples above use fairly low level Lean expressions to prove statements. Lean provides a very powerful, higher level DSL (domain specific language) for proving. You enter the Tactic DSL using `by`.

Proving results uses the super `sorry` keyword. Here is an example of Tactics and sorry. 
```lean
example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  intro h hp
  have hpq := h.left
  have hqr := h.right
  exact hqr (hpq hp)
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

## Programming

Lean is also a full-fledged functional programming language. For example, much of Lean is programmed in Lean (and then compiled). That said, the Lean Programming Language is not really general purpose: You would probably lose your mind trying to build an operating system with Lean. Rather, Lean is a programming language designed first for programming Lean itself, and second for build mathematical data structures and algorithms.

If you are not familiar with functional programming: you will be by then end of this book.

Here is an example program: 
```lean
def remove_zeros (L : List ℕ) : List ℕ := match L with
  | [] => List.nil
  | x::Q => if x = 0 then remove_zeros Q else x::(remove_zeros Q)

#check remove_zeros

#eval remove_zeros [1,2,3,0,5,0,0]
```
 Note the similarity between `def` and `theorem`. The latter is simply a special kind of definition.

## Documentation

- [Loogle](https://loogle.lean-lang.org/) - Google for Lean

- [Zulip Chat](https://leanprover.zulipchat.com/)

- [Lean Theorem Proving Book](https://lean-lang.org/theorem_proving_in_lean4/title_page.html)

- [Lean Functional Programming Book](https://lean-lang.org/functional_programming_in_lean/title.html)

- [Lean Metaprogramming](https://leanprover-community.github.io/lean4-metaprogramming-book/) -- Advanced!

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)

- [Tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)

- [The Standard Library](https://github.com/leanprover/lean4/blob/ffac974dba799956a97d63ffcb13a774f700149c/src/Init/Prelude.lean)



<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
