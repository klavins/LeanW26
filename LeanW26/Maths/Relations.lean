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
Binary Relations
===
-/

/-
Definition
===

A **binary relation** on a type `α` is a function `σ → α → Prop`.

-/

universe u
variable {α : Sort u} {β : Type u}
abbrev Rel := α → α → Prop


/-
Running Examples
===
-/

/- Order Like: -/
#check Nat.le               -- ℕ → ℕ → Prop
#check List.lt              -- List α → List α → Prop
#check Set.Subset           -- Set α → Set α → Prop

/- Lean's Connectives -/
#check And                  -- Prop → Prop → Prop
#check Or                   -- Prop → Prop → Prop

/- Equality -/
#check Eq                   -- Prop → Prop → Prop

/- Tail Equivalence on Sequences -/
def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n > m, σ₁ n = σ₂ n



/-
Reflexivity
===
A relation `R` is reflexive if `R x x` for all `x`.
-/

def Refl (R : α → α → Prop) := ∀ x, R x x

/- Applying this definition to our examples:  -/

example :  Refl Nat.le                := by intro n; simp
example :  Refl (Set.Subset (α := β)) := fun _ _ hx => hx
example : ¬Refl And           := fun h => by simpa using (h False)
example : ¬Refl Or            := fun h => by simpa using (h False)
example :  Refl (Eq (α := ℕ))         := fun _ => rfl
example :  Refl (te (α := α))         := fun _ => ⟨ 0, fun _ _ => rfl ⟩

/- The list example requires some extra work. We have to show we are applying
it to a type for which the typeclass `LT` has been intantiated. -/

example [hl : LT β] : ¬Refl (List.lt (α := β)) :=
  fun h => by simpa using (h [])

/-
Symmetry
===
A relation `R` is symmetric if `R x y → R y x` for all `x` and `y`.
-/

def Symm (R : α → α → Prop) := ∀ x y, R x y → R y x

/- For example: -/

example : ¬Symm Nat.le := fun h => by simpa using (h 0 1 (by simp))
example :  Symm And    := fun _ _ ⟨ hx, hy ⟩ => ⟨ hy, hx ⟩

example :  Symm (te (α := α)) := by
  intro σ₁ σ₂ ⟨ m, hm ⟩
  use m
  intro n hn
  exact Eq.symm (hm n hn)


/-
Antisymmetry
===
A relation `R` is antisymmetric if `R x y → R y x → x = y` for all `x` and `y`
-/

def AntiSymm (R : α → α → Prop) := ∀ x y, R x y → R y x → x = y

/- For example: -/

example : AntiSymm (Set.Subset (α := β)) := by
  intro A B hAB hBA
  ext x
  exact ⟨ fun hx => hAB hx, fun hy => hBA hy ⟩

example : ¬AntiSymm (te (α := ℕ)) := by
  intro h
  let f n := if n < 2 then 0 else n
  have heq := h f id ⟨ 2, by grind ⟩ ⟨ 2, by grind ⟩
  have hne : f 1 ≠ id 1 := by grind
  have heq : f 1 = id 1 := by grind
  grind


/-
Transitivity
===
A relation `R` is transitive if `R x y → R y z → R x z` for all `x`, `y` and `z`.
-/

def Trans (R : α → α → Prop) := ∀ x y z, R x y → R y z → R x z

/- For example, -/

example : Trans (Set.Subset (α := β)) := by
  intro _ _ _ hAB hBC _ hA
  exact hBC (hAB hA)

/- or -/

example : Trans And := by
  intro p q r ⟨ hp, hq ⟩ ⟨ hq, hr ⟩
  exact ⟨ hp, hr ⟩

/- Here's one that is not transitive -/

example : ¬Trans (Ne (α := ℕ)) := by
  intro h
  have h12 : 1 ≠ 2 := by decide
  have := h 1 2 1 h12 h12.symm
  simp_all


/-
Exercises
===

<ex /> Do the remaining examples left undone on the slide about symmetry.

<ex /> Do the remaining examples left undone on the slide about antisymmetry.

<ex /> Do the remaining examples left undone on the slide about transitivity.

-/

/-
The Reflexive Closure
===
The **reflexive closure** of `R` is the smallest reflexive relation containing `R`.
It can be defined:

-/

inductive ReflC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → ReflC R x y
  | refl {x} : ReflC R x x

/- We can show this definition is reflexive, contains `R` and is the smallest such relation: -/

theorem is_refl {R : α → α → Prop} : Refl (ReflC R) := by
  intro x
  exact ReflC.refl

theorem contains {R : α → α → Prop} {x y : α} : R x y → ReflC R x y := by
  exact ReflC.base

theorem is_smallest {R S : α → α → Prop} (hr : ∀ x, S x x) (hi : ∀ {x y}, R x y → S x y)
  : ∀ {x y}, ReflC R x y → S x y  := by
  intro x y h
  cases h with
  | base hb => exact hi hb
  | refl => exact hr x


/-
Example Reflexive Closure
===

We can show `≤` is the reflexive closure of `<`:
-/

example {x y : ℕ} : ReflC (Nat.lt) x y ↔ x ≤ y := by
  constructor
  · intro h
    cases h with
    | base h1 =>
      exact Nat.le_of_succ_le h1
    | refl =>
      aesop
  · intro h
    cases h with
    | refl =>
      exact ReflC.refl
    | step h1 =>
      exact ReflC.base (by aesop)

/-
Other Closures
===
Similarly we can define
-/

/- **Symmetric Closure**: -/
inductive SymmC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → SymmC R x y
  | symm {x y} : R x y → SymmC R y x

/- **Transitive Closure**: -/
inductive TransC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → TransC R x y
  | trans {x y z} : R x y → TransC R y z → TransC R x z


/-
Exercises
===
-/

/-
Equivalent Expressions
===

Induction and closures allow us to define fairly sophisticated relations.

For example, suppose we define a simple set of expressions

-/

inductive Expr where
  | zero
  | one
  | add : Expr → Expr → Expr

infixl:60 " + " => Expr.add

open Expr

/-
We mean the same thing when we write, for example,
-  (one+zero)+one
-  one+one
But how do we define that these are equivalent?
-/

/-
Equality on Expressions
===
-/

inductive Expr.eq : Expr → Expr → Prop where

  -- Core
  | assoc {a b c} : eq ((a+b)+c) (a+(b+c))
  | comm {a b} : eq (a+b) (b+a)
  | add_zero_right {a} : eq (a+zero) a
  | add_zero_left {a} : eq (zero+a) a

  -- Congruence
  | congr {a b c d} : eq a c → eq b d → eq (a+b) (c+d)

  -- Closures
  | refl {a} : eq a a
  | symm {a b} : eq a b → eq b a
  | trans {a b c } : eq a b → eq b c → eq a c

scoped infixl:50 " ~ " => Expr.eq

/-
Examples
===
As an example, here is a proof that the expressions `(1+0)+1` and `1+1` are equivalent.
-/

example : (one+zero)+one ~ one+one := by
  apply eq.congr
  · apply eq.add_zero_right
  · apply eq.refl

/- And here are some basic properties: -/

theorem cong_left {a b c : Expr} : a ~ b → a + c ~ b + c := by
  intro h
  exact eq.congr h eq.refl

theorem cong_right {a b c : Expr} : b ~ c → a + b ~ a + c := by
  intro h
  exact eq.congr eq.refl h

theorem cong_assoc_left {a b c a' b' : Expr}
  : a ~ a' → b ~ b' → (a + b) + c ~ (a' + b') + c := by
  intro ha hb
  apply cong_left
  exact Expr.eq.congr ha hb

theorem cong_assoc_right {a b c b' c' : Expr}
  : b ~ b' → c ~ c' → a + (b + c) ~ a + (b' + c') := by
  intro hb hc
  apply cong_right
  apply Expr.eq.congr hb hc

/- And another example: -/

theorem sub {a b c : Expr} : a ~ c → b ~ c → a ~ b := by
  intro h1 h2
  exact eq.trans h1 (eq.symm h2)

example {n : ℕ} : (add zero)^[n] zero ~ zero := by
  induction n with
  | zero => apply eq.refl
  | succ n ih =>
    unfold Nat.iterate
    have h1 := @eq.trans zero (zero.add^[n] zero) (zero.add^[n] (zero + zero)) (eq.symm ih)
    apply eq.symm
    apply h1
    have h2 : zero + zero ~ zero := by apply eq.add_zero_right

    sorry

/-
Soundness
===
We need to make sure we do not accidentlly
say two expressions are equal if they do not evaluate to the same thing.
To check this we define an eval function:
-/

def eval : Expr → Nat
  | zero => 0
  | one => 1
  | add a b => eval a + eval b

/- We can now check soundess by induction on the equivalence: -/

theorem sound (e f : Expr) : e ~ f → eval e = eval f := by
  intro h
  induction h with
  | assoc           => simp[eval,Nat.add_assoc]
  | comm            => simp[eval,Nat.add_comm]
  | add_zero_left   => simp[eval]
  | add_zero_right  => simp[eval]
  | congr ih1 ih2   => unfold eval; simp_all
  | refl            => simp
  | symm _ ih       => exact ih.symm
  | trans ih1 ih2   => simp[*]


/-
Exercises
===
-/

/-
Ordering
===
-/

/-
Equivalence
===
-/

/-
Setoids
===
-/

/-
Quotients
===
-/

/-
Exercises
===

</ex > Many textbooks define a relation as a subset of `Set (α × α)`. These
two notions are equivalent, and it is more idomatic in
type theory to use currying. Show the definitions are equivalent:

-/

def relation_defs_equiv {α : Type u} : (α → α → Prop) ≃ Set (α × α) := {
  toFun := sorry,
  invFun := sorry,
  right_inv := sorry,
  left_inv := sorry
}

def le : ℕ → ℕ → Prop
  | 0, y => y ≠ 0
  | k+1, j+1 => le k j
  | _,0 => False

/-
Exercise
===

<ex /> (Optional) Show that equivalence on `Expr` is complete:

-/

theorem complete {e f : Expr} : eval e = eval f → e ~ f := sorry

/-
One way to do this is to define a normal form `(1+(1+(1+0)))` for each
`Expr`, establish completness for normal forms as a `lemma`, and then
use transitivity to establish the desired result.
-/

--hide
end LeanW26
--nohide
