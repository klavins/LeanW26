--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26

--notdone

/-
Equality
===
-/

/-
Objects, Functions and Equality
===

We extend the first order logic to deal with functions of objects in our universe.
A critical components is a notion of **equality** between objects.

Astonishingly, Lean's equality is not a built in type, but is defined in the standard library.
Once we have equality, we can start working with statements
about functions and their relationships in earnest.

Equality is Defined Inductively
===

To lean how equality works, let's define our own version of it.
-/

universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

#check MyEq 1 2

example : MyEq 1 1 :=
  MyEq.refl 1

/- We can define notation -/

infix:50 " ~ "  => MyEq

#check 1 ~ 1

/-
Refl is Powerful
===

Terms that are beta-reducible to each other are considered definitionally equal.
You can show many of equalities automatically -/

example : 1 ~ 1 :=
  MyEq.refl 1

example : 2 ~ (1+1) := by
  apply MyEq.refl

example : 9 ~ (3*(2+1)) := by
  apply MyEq.refl

/-
These proofs do not use rules of arithmetic like associativity.
The use proof by computation (reducibility). So
```lean
| refl a : MyEq a a
```
works for any two definitionally equivalent forms of `a`.

-/

/-
Substitution
===

Substitution is the second most critical property of the equality.
It allows us to conclude, for example, that if `x = y` and `p x` then `p y`. -/

theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl => exact h₂

/- In this example we substitute `y` for `x` to prove equality between two propositions. -/

example {x y : Nat} : x ~ y → (x > 2 ↔ y > 2) := by
  intro h
  apply MyEq.subst h       -- goal becomes x > 2 ↔ x > 2
  exact ⟨ id, id ⟩


/-
Symmetry and Transitivity
===
You can use substitution to show the standard properties we know and love about equality. -/

theorem MyEq.sym {α : Sort u} {a b : α} : a ~ b → b ~ a := by
  intro h
  apply MyEq.subst h
  exact MyEq.refl a

theorem MyEq.trans {α : Sort u} {a b c : α} : a ~ b → b ~ c → a ~ c := by
  intro hab hbc
  exact MyEq.subst hbc hab

/- Here is an example showing the use of both of these theorems at once. -/

example {x y z : Nat} : y ~ x → z ~ y → x ~ z := by
  intro h1 h2
  apply MyEq.trans (MyEq.sym h1) (MyEq.sym h2)

/-
Congruence
===

Congruence is critical for equation solving.
-/

theorem MyEq.congr_arg {α : Sort u} {a b : α} {f : α → α} : a ~ b → f a ~ f b := by
  intro hab
  apply MyEq.subst hab
  exact MyEq.refl (f a)


/- For example, -/

example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 :=
  fun h => MyEq.congr_arg (f := fun w => 2*w + 1) h

/- Or, with tactics -/

example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 := by
  intro h
  apply MyEq.congr_arg (f := fun w => 2*w + 1)    -- goal becomes x ~ y
  exact h

/-
Lean's Equality
===

Lean's equality relation is called `Eq` and its notation is `=`,
as we have been using. Lean also defines `rfl` to be `Eq.refl _` -/

#print rfl
example : 9 = 3*(2+1) := Eq.refl 9
example : 9 = 3*(2+1) := rfl

/- Lean provides a long list of theorems about equality, such as -/

#check Eq.symm            -- a = b → b = a
#check Eq.subst           -- a = b → motive a → motive b
#check Eq.substr          -- b = a → p a → p b
#check Eq.trans           -- a = b → b = c → a = c
#check Eq.to_iff          -- a = b → (a ↔ b) when a and b are Prop
#check Eq.mp              -- α = β → α → β
#check Eq.mpr             -- α = β → β → α
#check congrArg           -- (f : α → β), a₁ = a₂ → f a₁ = f a₂
#check congrFun           -- f = g → ∀ (a : α), f a = g a
#check congr              -- (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂

/-
Exercises
===
-/

/-
Triangle
===

h ▸ e is a macro built on top of Eq.rec and Eq.symm definitions.
Given h : a = b and e : p a, the term h ▸ e has type p b. You can
also view h ▸ e as a "type casting" operation where you change the
type of e by using h. The macro tries both orientations of h. If
the context provides an expected type, it rewrites the expected
type, else it rewrites the type of e`. See the Chapter "Quantifiers
and Equality" in the manual "Theorem Proving in Lean" for
additional information.

-/


theorem of_eq_true1 {p : Prop} (h : p = True) : p := by
  rw[h]
  exact True.intro

theorem of_eq_true2 {p : Prop} (h : p = True) : p :=
  Eq.mpr h True.intro          -- α = β     → β         → α
                               --   h    True.intro       p

theorem of_eq_true3 {p : Prop} (h : p = True) : p :=
  h ▸ True.intro

/-
Rewriting
===
-/

/- `rw[h]`: Rewrites the current goal using the equality h. -/
theorem t1 (a b : Nat) : a = b → a + 1 = b + 1 := by
  intro hab
  rw[hab]

/- The `rw` tactic is doing a searching for pattern matches and then using
the basic theorems about equality. -/

#print t1      -- theorem LeanW26.t1 : ∀ (a b : ℕ), a = b → a + 1 = b + 1 :=
               -- fun a b hab ↦ Eq.mpr (id (congrArg (fun _a ↦ _a + 1 = b + 1)
               -- hab)) (Eq.refl (b + 1))

/-
More Rewriting
===
-/

/- To use an equality backwards, use ← (written \left)-/
theorem t2 (a b c : Nat) : a = b ∧ a = c → b + 1 = c + 1 := by
  intro ⟨ h1, h2 ⟩
  rw[←h1, ←h2]

/- You can also rewrite assumptions using `at`. -/

example (a b c : Nat) : a = b → a = c → b + 1 = c + 1 := by
  intro h1 h2
  rw[h1] at h2
  rw[h2]

/- Rewrite variants include -/

#help tactic rewrite          -- rewrite without rfl at the end
#help tactic nth_rewrite      -- rewrite a specific sub-term

/-
Conv
===
-/

/-
Calc
===
-/

/-
The Simplifier
===
-/

/- The simplifier uses equations and lemmas to simplify expressions -/

theorem t3 (a b : Nat) : a = b → a + 1 = b + 1 := by
  simp

#print t3

/- Sometimes you have to tell the simplifer what equations to use. -/

theorem t4 (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by
   simp only[h1,h2,h3,h4,Nat.add_comm]

#check Nat.add_comm

/-
Exercise
===

<ex /> TBD

/-

<ex />
Show the following result using induction. -/

example (n : Nat) : 6 * (S n) = (n * (n+1)) * (2*n+1) :=
  sorry


/-
Inequality
===

Every inductive type comes with a theorem called `noConfusion`
that states that different constructors give different objects. -/

inductive Person where | mary | steve | ed | jolin
open Person

example : mary ≠ steve := by
  intro h
  exact noConfusion h

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

example : MyNat.zero ≠ MyNat.zero.succ := by
  intro h
  exact MyNat.noConfusion h

/-
Reasoning using noConfusion
===

Continuing the above example, suppose we want to specify who is on who's right side. -/

def on_right (p : Person) := match p with
  | mary => steve
  | steve => ed
  | ed => jolin
  | jolin => mary

def next_to (p q : Person) := on_right p = q ∨ on_right q = p

example : ¬next_to mary ed := by
  intro h
  cases h with
  | inl hme => exact noConfusion hme
  | inr hem => exact noConfusion hem

example : ∀ p , p ≠ on_right p := by
  sorry

/-
Trival
===

The `trivial` tactic actually figures out when to apply noConfusion-/

theorem t10 : ed ≠ steve := by
  intro h
  trivial


Exercises
===
-/

--hide
end LeanW26
--nohide
