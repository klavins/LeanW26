--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26




/-
Propositional Connectives
===

Overview
===
Inductive types capture all of propositional logic, first order logic, and more.

Instead of defining _and_, _or_ and the other logical connectives as
built-in operators in CIC, they are just defined terms of more primitive inductive types.

In this slide deck we redefine the connectives, to understand how they work.
To avoid naming conflicts with Lean's standard library, we open a namespace.

-/

namespace Temp

variable (p q r : Prop)

/-
The Axiom Rule
===

Not to be confused with Lean's `axiom` keyword.

As discussed in the slide deck on Propositional Logic, the Axiom Rule is

```none
  AX  ——————————
       Γ,φ ⊢ φ
```
Here is a simple proof that `{hp:p} ⊢ p` in Lean using the Axiom rule: -/



example (hp : p) : p :=  hp

/- Putting your cursor at the beginning of the second like, you will see
```
hp : p
⊢ p
```
Which says, give we have a proof `hp` of `p`, we need show `p`.
This is easy, we just use `hp` itself.


Aside: def, theorem, example, lemma
===

By the CHI, note that `def` and `theorem`
are essentially the same from a type theory point of few. And `example` is
just a theorem without a name.

So in the above we could write:

-/

def prop_id (hp : p) := hp

theorem prop_id_thm (hp : p) : p := hp

example (hp : p) : p := hp

/- Also, `prop_id` is really just a special case of the identity function. -/

def my_id.{u} {α : Sort u} (x : α) : α := x

example (hp : p) : p := my_id hp

/- So if you can write code in Lean you can prove theorems! -/

/-
Implication in Lean
===

**`→-Intro` is lambda abstraction:** Whenever you see a goal of the form `A → B`, you
write a lambda to get a simpler goal.
-/

example (hp : p) : q → p :=
  fun hq => sorry

example (hp : p) : q → p :=
  fun hq => hp

/-
**`→-Elim` is lambda application:** When you see function (with type `A → B`) in a context
you can apply it to get a simpler goal.
-/

example (hpq : p → q) (hp : p) : q :=
  hpq sorry

example (hpq : p → q) (hp : p) : q :=
  hpq hp

/-
And is an Inductive Type
===

Recall the inference rule
```none
                 Γ ⊢ φ   Γ ⊢ ψ
    ∧-Intro ———————————————————
                  Γ ⊢ φ ∧ ψ
```

It states that whenever we know propositions `φ` and `ψ`, then we know `φ ∧ ψ`.
From the point of view of types,
it says that if `φ` and `ψ` are of type `Prop`, then so is `φ ∧ ψ`.

We can write this as an inductive type definition as follows. -/

inductive And (φ ψ : Prop) : Prop where
  | intro : φ → ψ → And φ ψ

/- You can think of `h : And p q` as
- `h` has type `And p q`
- `h` is evidence that the type `And p q` is not empty
- `h` is a proof of the proposition `And p q`.

Proof of a Simple Proposition
===

Consider the proposition
```lean
p → q → And p q
```

As a type, this proposition is a function from `p to q` to `And p q`.
Thus, we know that an element of this type has the form
```lean
fun hp => fun hq => sorry
```

For the body of this lambda abstraction, we need to `introduce` an `And` type,
which requires proofs of `p` and `q` respectively. Using the inductive definition of `And` we get
```lean
fun hp hq => And.intro hp hq
```
-/

example (p q : Prop) : p → q → And p q :=
  fun hp => fun hq => And.intro hp hq

/-
And Elimination
===

The elimination rules for `And` are
```none
                Γ ⊢ φ ∧ ψ                          Γ ⊢ φ ∧ ψ
  ∧-Elim-Left ——————————————         ∧-Elim-Right —————————————
                  Γ ⊢ φ                              Γ ⊢ ψ
```
which we can write in Lean as -/

def And.left {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro hp _ => hp

def And.right {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro _ hq => hq

/-
Proofs with And-Elimination
===

With these inference rules, we can do more proofs: -/

example (p q : Prop) : (And p q) → p :=
  fun hpq => And.left hpq

example (p q : Prop) : (And p q) → (And q p) :=
  fun hpq => And.intro hpq.right hpq.left




/-
Match is Enough
===

The elimination rules above are a _convenience_ we defined to make the proof look
more like propositional logic. We could also have written: -/

example (p q : Prop) : (And p q) → p :=
  fun hpq => match hpq with
             | And.intro hp _ => hp

/- That is, `match` is a generic elimination rule. -/


/-
Lean's And
===

Lean's And is actually defined as a structure:
```lean
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```

The `intro ::` part renames the introduction rule `intro` instead of the default `mk`.

Lean also defines infix notation `∧`. So you can write

-/

end Temp -- stop using our temporary namespace and use Lean's And

variable (p q r : Prop)
#check p ∧ q

/-
Structures
===
With Lean's `And` we can do
-/

example : (p ∧ q) → (q ∧ p) :=
  fun hpq => And.intro hpq.right hpq.left

example : (p ∧ q) → (q ∧ p) :=
  fun hpq => { left := hpq.right, right :=  hpq.left }

example : (p ∧ q) → (q ∧ p) := fun hpq => ⟨ hpq.right, hpq.left ⟩

/- You can also match the the parts of a structure in the argument to `fun`: -/

example : (p ∧ q) → (q ∧ p) := fun ⟨ hp, hq ⟩ => ⟨ hq, hp ⟩

/-
which is defined in [Init.core](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#And.symm).
-/

/-
Exercise
===

<ex /> Show the following using a term level proof without using the library.

-/

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := sorry

--hide
namespace Temp
--unhide

/-
Or is Inductive
===

To introduce new `Or` propositions, we use the two introduction rules
```none
                 Γ ⊢ φ                              Γ ⊢ ψ
 ∨-Intro-Left ———————————          ∨-Intro-Right ————————————
               Γ ⊢ φ ∨ ψ                          Γ ⊢ φ ∨ ψ
```
In Lean, we have -/

inductive Or (φ ψ : Prop) : Prop where
  | inl (h : φ) : Or φ ψ
  | inr (h : ψ) : Or φ ψ

/- And we can use this inference rule in proofs as well. -/

example (p q : Prop) : And p q → Or p q :=
  fun hpq => Or.inr hpq.right

/-
Or Elimination
===

Recall the inference rule
```none
           Γ,p ⊢ r    Γ,q ⊢ r    Γ ⊢ p ∨ q
  ∨-Elim ————————————————————————————————————
                       Γ ⊢ r
```

It allows us to prove `r` given proofs that `p → r`, `q → r` and `p ∨ q`.
We can define this rule in Lean with: -/

def Or.elim {p q r : Prop} (hpq : Or p q) (hpr : p → r) (hqr : q → r) :=
  match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq

/-
Example of and Or-Elim Proof
===

Here is an example proof using or introduction and elimination. -/

example (p q : Prop): Or p q → Or q p :=
  fun hpq => Or.elim
      hpq                                 -- p ∨ q
      (fun hp => Or.inr hp)               -- p → (q ∨ p)
      (fun hq => Or.inl hq)               -- q → (q ∨ p)

/- Once again, the elimination rule is just a convenience and
the proof could have been written with `match`.

False is Inductive
===

Finally, we have `False`, which has no introduction rule, kind of like `Empty`,
except we add the requirement that `False` is also type of `Prop`.  -/

inductive False : Prop

/- From False we get the `Not` connective, which is "syntactic sugar". -/

def Not (p : Prop) : Prop := p → False

/- Here is an example proof: -/

example (p q : Prop) : (p → q) → (Not q → Not p) :=
  fun hpq hq => fun hp => hq (hpq hp)

/-
False Elimination
===

To define the elimination rule for `False`
```
           Γ ⊢ ⊥
  ⊥-Elim ——————————
           Γ ⊢ p
```
we take advantage of the fact that `False` was defined inductively. -/

def False.elim {p : Prop} (h : False) : p :=
  nomatch h

/- Here is an example proof that from False you can conclude anything: -/

example (p q : Prop) : And p (Not p) → q :=
  fun h => False.elim (h.right h.left)

/- This elimination rule provides another way to prove the example: -/

example : False → True :=
  False.elim




/-
If and only iff
===

If and only if is defined inductively as
```lean
structure Iff (p q : Prop) : Prop where
  intro ::
  mp : p → q → Iff p q
  mpr : q → p → Iff q p
```

For example:

-/

example : Iff p p := Iff.intro id id

/- or -/

example : Iff p p := { mp := id, mpr := id }

/- or -/

example : Iff p p := ⟨ id, id ⟩





/-
Notation
===

Lean defines notation like `∨` and `∧` for logic to make it look like math.
We won't redo that entire infrastructure here.
But to give a sense of it, here is how Lean defines infix
notation for `Or`, `And`, and `Not` notation.

```hs
infixr:30 " ∨ "  => Or
infixr:35 " ∧ "   => And
infixr:50 " ↔ "   => Iff
notation:max "¬" p:40 => Not p
```

The numbers define the precedence of the operations. So `v` has lower precedence than `∧`,
which has lower precedence than `¬`.

Now we can write: -/

end Temp -- start using Lean's propositions

example (p q : Prop) : (p ∧ (¬p)) → q :=
  fun h => False.elim (h.right h.left)

/-
<div class='fn'>
  <a href="https://github.com/leanprover/lean4/blob/master/src/Init/Notation.lean">
  Lean's core notation</a></div>

-/




/-
Exercise
===

<ex /> Show

-/

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := sorry

/-
<ex /> Do all these proofs, which are borrowed from the [Theorem Proving in Lean Book](https://lean-lang.org/theorem_proving_in_lean4/title_page.html). Use only term level proofs. No tactics.


 -/

example : p ∨ q ↔ q ∨ p := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬(p ∧ ¬p) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry

/-
<ex /> This one requires the law of the excluded middle, which can be
used with `Classical.em`. The way to do this one is to do Or-elimination
on `Classical.em p`.
-/

example : (p → q) → (¬p ∨ q) := sorry

/-
Exercise
===

<ex /> Consider the Not-Or operation also known as Nor. It has the following inference rules:
```none
                 Γ ⊢ ¬p   Γ ⊢ ¬q
  `Nor-Intro` ———————————————————
                  Γ ⊢ Nor p q


                    Γ ⊢ Nor p q                            Γ ⊢ Nor p q
  `Nor-Elim-Left` ——————————————         `Nor-Elim-Right` —————————————
                      Γ ⊢ ¬p                                 Γ ⊢ ¬q

```
Define these in Lean. Here is a start:

-/

inductive Nor (p q : Prop) : Prop where
  | intro : ¬p → ¬q → Nor p q

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) : Prop := sorry
def Nor.elim_right {p q : Prop} (hnpq : Nor p q) : Prop := sorry

/-
Exercise
===

<ex /> Use your `Nor` inference rules, and the regular inference rules from Lean's
propopsitional logic, to prove the following examples.
*Do not* use classical logic for these.

-/

example (p : Prop) : ¬p → (Nor p p) := sorry
example (p q : Prop) : (Nor p q) → ¬(p ∨ q) := sorry
example (p q : Prop) : ¬(p ∨ q) → (Nor p q) := sorry

/-
References
===

- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html

- Homotypy Type Theory Book
  https://homotopytypetheory.org/book/
  Chapter 5 covers inductive types

-/

--hide
end LeanW26
--unhide
