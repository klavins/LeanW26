
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Tactics.lean'>Code</a> for this chapter</span>
 # Tactics

Tactic mode is entered in a proof using the keyword `by`

```lean
variable (p : Type → Prop)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  sorry
```
 ## The `intro` Tactic

Introducion applies to implications and forall statements, introducing either a new hypothesis or a new object. It takes the place of `λ h₁ h₂ ... => ...`

Note also that by using `.` and indentation, you can visually break up your proof to it is more readable. 
```lean
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro hnep x
    sorry
  . intro hanp
    sorry
```
 ## The `apply` and `exact` Tactics

The `apply` tactic applies a function, forall statement, or another theorem. It looks for arguments that match its type signature in the context and automatically uses them if possible. 
```lean
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h (Exists.intro x hp)
  . intro h hepx
    apply Exists.elim hepx
    intro x hpa
    exact (h x) hpa

example (p : Nat → Prop) (h : ∀ (x : Nat) , p x) : p 14 := by
  apply h

theorem my_thm (q : Prop) : q → q := id

example (q : Nat → Prop) : (∀ x, q x) → ∀ x, q x := by
  apply my_thm
```
 `exact` is a variant of apply that requires you to fill in the arguments you are using. It essentially pops you out of tactic mode. It is used at the end of proofs to make things more clear and robust to changes in how other tactics in the proof are applied. 
```lean
example (p : Nat → Prop) (h : ∀ (x : Nat) , p x) : p 14 := by
  exact h 14
```
 ## The `assumption` Tactic

This tactic looks through the context to find an assumption that applies, and applies it. It is like apply but where you don't even say what to apply. 
```lean
example (c : Type) (h : p c) : ∃ x, p x := by
  apply Exists.intro c
  assumption
```
 ## Structures

Structures in Lean are a way to package data. They are a kind of inductive type, but presented differently. For example, 
```lean
structure Point where
  x : Int
  y : Int
```
 You can make new points in a variety of ways 
```lean
def p₁ := Point.mk 1 2
def p₂ : Point := { x := 1, y := 2 }
def p₃ : Point := ⟨ 1,2 ⟩
```
 ## Packaging and Exists

In Lean, And is a structure (not a simple inductive type, like I originally described). 
```lean
#print And

example (p : Prop): p → (p ∧ p) :=
  λ hp => ⟨ hp, hp ⟩
```
 This notation also works with inductive types though, as with Exists. 
```lean
#print Exists

example (p : Type → Prop) (c : Type) : (∀ x, p x) → ∃ x, p x :=
  λ h => ⟨ c, h c ⟩

example : ∃ (p : Point) , p.x = 0 :=  by
  exact ⟨ ⟨ 0, 0 ⟩, rfl ⟩
```
 ### Tactics Produce Low Level Proofs 
```lean
theorem t (p : Type → Prop) (c : Type) : (∀ x, p x) → ∃ x, p x := by
  intro h
  exact ⟨ c, h c ⟩

#print t
```
 ## Pattern Matching

You can match constructors with intro to more easily break up expressions. 
```lean
example (p q : Prop) : p ∧ q → q := by
  intro ⟨ _, hq ⟩
  exact hq

example : (∃ x , ¬p x) → ¬ ∀ x, p x := by
  intro ⟨ x, hnp ⟩ hnap
  exact hnp (hnap x)

example (P Q : Type → Prop): (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨ x, ⟨ hp, hq ⟩ ⟩
  exact ⟨ x, ⟨ hq, hp ⟩ ⟩
```
 ## Getting Help with Apply?

You can ask Lean to try to find someting to apply with `apply?` 
```lean
example : (∃ x , ¬p x) → ¬ ∀ x, p x := by
  intro ⟨ x, hnp ⟩ hnap
  apply?
```
 It doesn't always work though. 
 ## FOL Examples Revisited

Now that we can use tactics, our First Order Logic Proofs can be made to look a little cleaner, although one might argue the use of angled brackets is harder to read. 
```lean
variable (p: Type → Prop)
variable (r : Prop)

theorem asd : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h (Exists.intro x hp)
  . intro hp ⟨ x, hnp ⟩
    exact hp x hnp

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro ⟨ x, ⟨ hx, hr ⟩ ⟩
    exact ⟨ ⟨ x, hx ⟩ , hr ⟩
  . intro ⟨ ⟨ x, hx ⟩ , hr ⟩
    exact ⟨ x, ⟨ hx, hr ⟩ ⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h x hp
    exact h ⟨ x, hp ⟩
  . intro h ⟨ x, hp ⟩
    exact h x hp
```
 ## The `have` and `let` Tactics

You can use `have` to record intermediate results 
```lean
example (p q : Prop) : p ∧ q → p ∨ q := by
  intro ⟨ h1, h2 ⟩
  have hp : p := h1
  exact Or.inl hp
```
 If you need an intermediate value, you should use `let`. 
```lean
example : ∃ n , n > 0 := by
  let m := 1
  exact ⟨ m, Nat.one_pos ⟩
```
 ## Cases

The cases tactic wraps around Or.elim to make proofs easier to read. 
```lean
example (p q : Prop) : (p ∨ q) → q ∨ p  := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.symm (Or.inr hq)

-- Cases doesn't always buy you much. You can just apply Or.elim.
example (p q : Prop) : (p ∨ q) → q ∨ p  := by
  intro h
  apply Or.elim h
  . intro hp
    exact Or.symm h
  . intro hq
    exact Or.symm h
```
 ## Cases Works With any Inductive Ttype

Here's are some somewhat longwinded ways to prove some simple results 
```lean
variable (P Q : Type → Prop)

example : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  cases h with
  | intro x h => exact ⟨ x, And.symm h ⟩

example (p q : Prop) : (p ∧ q) → (p ∨ q) :=  by
  intro h
  cases h with
  | intro hp hq => exact Or.inl hp
```
 ## The `by_cases` Tactic

The cases tactic is not to be confused with the `by_cases` tactic, which uses `classical reasoning`. 
```lean
example (p : Prop): p ∨ ¬p := by
  by_cases h : p
  . exact Classical.em p -- assuming h : p
  . exact Classical.em p -- assuming h : ¬p
```
 # The `induction` Tactic

Proof by induction works for all inductive types. It is similar to using cases, but it adds an `inductive hypothesis` where needed.

As an example, consider the natural numbers and suppose P : Nat → Prop is a property. To prove P with induction, you do :

- **BASE CASE**: P(0)
- **INDUCTIVE STEP**: ∀ n, P(n) → P(n+1) 
```lean
def E (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ x => ¬E x

example : ∀ n : Nat, E n ∨ E n.succ := by
  intro n
  induction n with
  | zero => exact Or.inl trivial
  | succ k ih =>
    apply Or.elim ih
    . intro h1
      exact Or.inr (by exact fun a ↦ a h1)
    . intro h3
      exact Or.inl h3
```
 ## Tactic Documentation

There are a lot of tactics:

  https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md



<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
