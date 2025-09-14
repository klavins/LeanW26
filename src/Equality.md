
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Equality.lean'>Code</a> for this chapter</span>
 # Objects, Functions and Equality

In this chapter we extend the first order logic discussed in the last chapter to deal with functions of objects in our universe. On one of the critical components is a notion of equality between objects. Astonishingly, Lean's equality is not a built in type, but is defined in the standard library. Once we have equality, we can start working with statements about functions and their relationships in earnest.

## Equality is a Binary Relation Defined Inductively 
```lean
universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

#check MyEq 1 2

example : MyEq 1 1 :=
  MyEq.refl 1
```
 We can define some notation 
```lean
infix:50 " ~ "  => MyEq

#check 1 ~ 1
```
 ### Refl is Powerful

In Lean, terms that are beta-reducable to each other are considered definitionally equal. You can show a lot of equalities automatically 
```lean
example : 1 ~ 1 :=
  MyEq.refl 1

example : 2 ~ (1+1) := by
  apply MyEq.refl

example : 9 ~ (3*(2+1)) := by
  apply MyEq.refl
```
 ### Substitution

Substition is the second most critical property of the equality. It allows us to conclude, for example, that if x = y then p x is equal to p y. 
```lean
theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl => exact h₂
```
 You can use this theorem to show the standard properties we know and love about equality. 
```lean
theorem my_symmetry (a b : Type): a ~ b → b ~ a := by
  intro h
  apply MyEq.subst h
  exact MyEq.refl a

theorem my_transitivity (a b c : Type) : a ~ b → b ~ c → a ~ c := by
  intro hab hbc
  exact MyEq.subst hbc hab

theorem my_congr_arg (a b : Type) (f : Type → Type) : a ~ b → f a ~ f b := by
  intro hab
  apply MyEq.subst hab
  exact MyEq.refl (f a)
```
 ## Lean's Equality

Lean's equality relation is called `Eq` and its notation is `=`, as we have been using. Lean also defines `rfl` to be `Eq.refl _` 
```lean
#print rfl
example : 9 = 3*(2+1) := Eq.refl 9
example : 9 = 3*(2+1) := rfl
```
 Lean provides a long list of theorems about equality, such as 
```lean
#check Eq.symm
#check Eq.subst
#check Eq.substr
#check Eq.trans
#check Eq.to_iff
#check Eq.mp
#check Eq.mpr

#check congrArg
#check congrFun
#check congr
```
 ### Tactics for Equality 
 rw[h]: Rewrites the current goal using the equality h. 
```lean
theorem t1 (a b : Nat) : a = b → a + 1 = b + 1 := by
  intro hab
  rw[hab]

#print t1
```
 To use an equality backwards, use ← (written \left)
```lean
theorem t2 (a b c : Nat) : a = b ∧ a = c → b + 1 = c + 1 := by
  intro ⟨ h1, h2 ⟩
  rw[←h1, ←h2]

#print t2
```
 You can also rewrite assumptions using `at`. 
```lean
example (a b c : Nat) : a = b ∧ a = c → b + 1 = c + 1 := by
  intro ⟨ h1, h2 ⟩
  rw[h1] at h2
  rw[h2]
```
 ## The Simplifier 
 The simplifier uses equations and lemmas to simplify expressions 
```lean
theorem t3 (a b : Nat) : a = b → a + 1 = b + 1 := by
  simp

#print t3
```
 Sometimes you have to tell the simplifer what equations to use. 
```lean
theorem t4 (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by
   simp only[h1,h2,h3,h4,Nat.add_comm]


#check Nat.add_comm

#print t4
```
 ## The `linarith` Tactic

By importing Mathlib.Tactic.Linarith (see top of this file), you get an even more powerful simplifier.


```lean
example (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by linarith

example (x y z : ℚ)
 (h1 : 2*x - y + 3*z = 9)
 (h2 : x - 3*y - 2*z = 0)
 (h3 : 3*x + 2*y -z = -1)
 : x = 1 ∧ y = -1 ∧ z = 2 := by
 apply And.intro
 . linarith
 . apply And.intro
   . linarith
   . linarith
```
 ### Example : Induction on Nat

As an example the brings many of these ideas together, consider the sum of the first `n` natural numbers, which is `n(n+1)/2`. A proof by induction would be:

- **BASE CASE**: `0 = 0*1/2`
- **NDUCTIVE STEP**: `∀ k, Sum k = k(k+1)/2 → Sum (k+1) = (k+1)(k+2)/2`

We can do this in lean with the `induction` tactic. 
```lean
def S (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n + S x

#eval S 3

example : ∀ n, 2 * S n = n*(n+1) := by
  intro n
  induction n with
  | zero => simp[S]
  | succ k ih =>
    simp[S,ih]
    linarith
```
 ## Inequality

Every inductive type comes with a theorem called noConfusion that states that different constructors give different objects. 
```lean
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
```
 Continuing the above example, suppose we want to specify who is on who's right side. 
```lean
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
```
 Note: The `trivial` tactic actually figures out when to apply noConfusion
```lean
theorem t10 : ed ≠ steve := by
  intro h
  trivial

#print t10

#help tactic trivial
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
