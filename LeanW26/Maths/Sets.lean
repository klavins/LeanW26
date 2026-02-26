--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26

/-
Sets
===
-/

/-
Types vs Sets
===

Type theory and set theory are different foundational theories for mathematics.

**Types**
- A judgement `x : α` is a primitive
- Membership is defined by typing rules
- A type is a syntactic object
- Predicates are types

**Sets**
- Membership `∈` is primitive
- Membership is defined by a predicate
- A set is a semantic object
- Predicates are meta-logical formulas

At best we can only simulate sets in type theory using definitions and notation.


Types as Sets
===

**Option 1:** Express sets directly as types

- Membership `x ∈ S` is `x : S`

- Subsets are subtypes
```
class Subtype {α : Sort u} (p : α → Prop)
  val : α
  property : p val
```

For example:

-/

def Evens := Subtype (fun n => ∃ k, n = 2*k)
example : Evens := ⟨ 14, by use 7 ⟩

/- In fact, Lean defines nice syntax for `Subtype`, which looks like set builder notation.  -/

def Evens' := { n // ∃ k, n = 2*k }
example : Evens' := ⟨ 14, by use 7 ⟩

/-
Uses of Subtypes
===

Many objects in Lean and Mathib are defined as subtypes:

-/

#print NNRat               -- def NNRat : Type := { q : Rat // 0 ≤ r }
#print NNReal              -- def NNReal : Type := { r : Real // 0 ≤ r }
#print SpecialLinearGroup  -- def ... := ... fun R V ... ↦ { u // LinearEquiv.det u = 1 }

/-
And the basic pattern of including a predicate in a structure is common, as in:
```lean
structure Subgroup (G : Type u) [Group G] where
  p : G → Prop
  one_in : p 1
  inv_in : p x → p x⁻¹
  mul_in : p a → p b → p a * b
```

These kinds of constructions allow you to package the proof that an element is a
member of the `Subtype` in the sub type itself.

-/



/-
Issues with Types as Sets
===

Defining set operations is at best complicated:
-/


--hide
namespace Temp
--unhide

def Subtype.Intersection.{u} {α : Type u} {p q : α → Prop}
  (A : Type u) (B : Type u){_hA : A = Subtype p} {_hB : B = Subtype q} :=
  { x // p x ∧ q x }

/- For example, given -/

def A := { n // n > 4 }
def B := { n // n > 5 }

/- here is `A ∩ B`: -/

def C := Subtype.Intersection (p := (· > 4)) (q := (· > 5))
  (_hA := by simp[A]) (_hB := by simp[B]) A B

/- Now to show that, for exampe `6 ∈ A ∩ B`, we do: -/

example : C := ⟨ 6, ⟨ by simp, by simp ⟩ ⟩

--hide
end Temp
--unhide

/-
Exercise
===

<ex /> Define

-/

def Evens.add (x y : Evens) : Evens := sorry

/- and prove -/

def Evens.add_assoc {x y z : Evens}
  : add x (add y z) = add (add x y) z := sorry

/-
Predicates as Sets
===

**Option 2**: In `def A := { n // n > 4 }` the predicate `n>4` is buried in the expression.
What if we just used use the predicate directly, as in
-/

def A (n : ℕ) := n > 4
def B (n : ℕ) := n > 5

/- and then put -/

def C (n : ℕ) := A n ∧ B n

/- whch looks quite close to `C = A ∩ B`. -/


/-
How the Mathlib's Set Library is Defined
===
Let's rebuild the set library.
<div class='fn'>Everything below is in a temporary namespace to avoid conflicts.</div>

-/

--hide
namespace Temp2
--unhide

def Set (α : Type) := α → Prop

def Set.member {α : Type} (x : α) (S : Set α) := S x
def Set.inter {α : Type} (A B : Set α) (x : α) := A x ∧ B x
def Set.union {α : Type} (A B : Set α) (x : α) := A x ∨ B x

scoped infix:20 " ∈ " => Set.member
scoped infixl:60 " ∩ " => Set.inter
scoped infixl:40 " ∪ " => Set.union

/-
Example Revisited
===
Using the new definitions, we can write:
-/

def A : Set ℕ := (· > 4)
def B : Set ℕ := (· > 5)

example : 6 ∈ A ∩ B := by   -- This is just the statement A 6 ∧ B 6
  apply And.intro
  · simp[A]
  · simp[B]

/-
The Subset Relation
===

The subset relation is just implication:
-/

def Set.subset {α : Type} (A B : Set α) : Prop := ∀ x, A x → B x

infixl:40 " ⊆ " => Set.subset

/- And proofs look like first order logic -/

example {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.left

/- In fact, using the `change` tactic, you can make the goal look like FOL: -/

example {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  change ∀ x, A x ∧ B x → A x
  intro x hx
  exact hx.left

/-
Proving Set Equalites
===

To show two sets are equal, it is enough to show each is a subset of the other.

This theorem uses the axiom `propext` which says `∀ {a b : Prop}, (a ↔ b) → a = b`

-/

theorem subset_antisymm_iff {α : Type} {A B : Set α}
  : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  apply Iff.intro
  · intro h
    simp only [h, and_self]
    intro x hx
    exact hx
  · intro ⟨ ha, hb ⟩
    funext x
    apply propext
    exact ⟨ ha x, hb x ⟩

/- The name `antisym` comes from the observation that the subset relation is *antisymmetric*. -/

/-
An Example Set Equality
===
-/

example {α : Type} (A B : Set α) : A ∩ B = B ∩ A := by
  apply subset_antisymm_iff.mpr
  apply And.intro
  · intro x hx
    exact ⟨ hx.right, hx.left ⟩
  · intro x hx
    exact ⟨ hx.right, hx.left ⟩


/-
Complements and Differences
===
Complements and differences are what you would expect.
-/

def Set.uninv {α : Type} : Set α := fun _ => True
def Set.compl {α : Type} (S : Set α) := fun x => ¬S x
postfix:95 " ᶜ " => Set.compl
def Set.diff {α : Type} (A B : Set α) := A ∩ Bᶜ
infixl: 55 " - " => Set.diff  -- Lean uses `\` but I couldn't get that to work

/- For example, we can show the relationship between compliment and universe. -/

example {α : Type} {A : Set α} : Aᶜ = Set.univ - A := by
  apply subset_antisymm_iff.mpr
  constructor
  · intro x hx
    constructor
    · trivial
    · exact hx
  · intro x ⟨ _, hc ⟩
    exact hc

/-
Powersets
===
The set of all subsets of a set can be defined using the subset relation:
-/

def Set.power {α : Type} (S : Set α) : Set (Set α) := fun A => A ⊆ S

/- Here is a nice example property: -/

example {α : Type} (A B : Set α)
  : A ⊆ B → Set.power A ⊆ Set.power B := by
  intro hab S hS x Sx
  apply hab
  apply hS
  exact Sx

/- This operation and many more are defined in Mathlib's *extensive* `Set` Library:
- [Definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html)
- [Set Operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Operations.html)
- [Basic Properties](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html)

-/

--hide
end Temp2
--unhide

/-
Set Builder Notation
===

Mathlib provides a powerful set builder notation.

For example:

-/

#check { n : ℕ  | n > 2 }
#check fun n => n > 2

#check { 2*n | n > 2 }
#check fun x => ∃ n > 2, 2*n = x

#check { (x,y) | Prime x ∧ Prime y ∧ x + 1 = y }
#check fun p : ℕ × ℕ => Prime p.1 ∧ Prime p.2 ∧ p.1 + 1 = p.2


/-
Exercises
===
-/

universe u
variable (α β : Type u) {A B C : Set α} {D E : Set β}

/-
<ex /> Using first order logic (and not Mathlib's set theorems), show:

-/

example : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := sorry
example : A ⊆ B → B ⊆ C → A ⊆ C := sorry

/- <ex /> Lean defines the image of `f` with respect to `A`, denoted `f '' A`,
to be the set `{f x | x ∈ A}`. Show:

-/

example {f : α → β} : f '' (A ∪ B) = f '' A ∪ f '' B := sorry

/- <ex /> Lean defines the preimage of `f` with respect to `A`, denoted
`f⁻¹' A` to be the set `{x | ∃ y, f x = y}`. Show,

-/

example {f : α → β} : f⁻¹' (D ∩ E) = f⁻¹' D ∩ f⁻¹' E := sorry


/-
Finite Sets
===

Defining a type for *finite* sets is an interesting challenge. Here are some options:

- **Finite types**
    - Define `Fin n := {0,1,2,...,n-1}`
    - Define typeclass `Fintype α` as having a bijection `α ≃ Fin n`
    - Cons: subsets, unions, etc are hard to define

- **Lists**
    - Create a structure with a `List` and a property requiring no duplicates
    - Cons: List equality depends on ordering

- **Equivalence Classes of Lists** (Lean's Approach)
    - Define perumutation an equivalence relation between lists
    - Take the quotient
    - Pros: It works
    - Cons: It's complicated

-/

/-
Fin
===

The easiest way to make a type that has exactly `n` elements is:

-/

--hide
namespace Temp3
--unhide

structure Fin (n : ℕ) where
  val : ℕ
  isLt : val < n

example : Fin 5 := ⟨ 3, by decide ⟩

--hide
end Temp3
--unhide

/-
Lean defines quite a bit of infrastructure around this type. For example,
-/

def x : Fin 10 := 1
def y : Fin 10 := 2

#eval 2*x + y               -- 4

/- Although it doesn't always do what you would expect : -/

#eval x + 10*y              -- 1 (modular addition)

/- But what if we want a finite type that has any type of element, not just integers?


Finite Types
===

We can definte a typeclass that registers a type `α` as finite by exhibiting a
bijection between `Fin n` and `α`. We wrap this into a `Prop`-valued typeclass
as follows:

-/

class inductive Finite (α : Type u) : Prop where
  | intro {n : ℕ} : α ≃ Fin n → Finite α

/- For example -/

inductive Spin where | up | dn

def Spin.equiv_fin2 : Spin ≃ Fin 2 := {
  toFun x   := match x with | up => 0 | dn => 1,
  invFun n  := match n with | 0 => up | 1 => dn,
  right_inv := by grind,
  left_inv  := by grind
}

instance Spin.is_finite : Finite Spin := ⟨ Spin.equiv_fin2 ⟩

/-
Lean's Finset
===

A `Finset` in Lean is a finite collection of elements all of the same type with
set-like operations:
-/

def R : Finset ℚ := {1/2, 1/4, 1/8, 1/16}
def S : Finset ℚ := {-3,-2,-1,0,1,2,3}

#eval R ∩ S
#eval R \ S

#eval insert 4 (insert (-4) R)       --  {-4,-3,-2,-1,0,1,2,3,4}


/- Under the hood, a `Finset` is a structure: -/

def X : Finset ℕ := {
  val := [1,2,3],                      -- A `Multiset`, which derives from a `List`
  nodup := by simp                     -- A proof the list has no duplicates
}

/-
In general you do not have a set defined by a predicate, or operations like
-/

#check_failure Rᶜ
#check_failure ({ n : ℕ | n < 10 } : Finset ℕ)


/-
Exercises
===

<ex /> Prove the following properties of `Fin`:

-/

example : Fin 0 → False := sorry
example (x : Fin 2) : x = 0 ∨ x = 1 := sorry
example (n : ℕ) (x y : Fin n) : x = y ↔ x.val = y.val := sorry

/-
<ex /> Define the equivalence

-/

def equiv_subtype {n : ℕ} : Fin n ≃ { x : ℕ | x < n } := sorry

/-
<ex /> Use the above equivalence to show

-/

theorem equiv_same_size {n m : ℕ} (eq : Fin n ≃ Fin m) : n = m := sorry

/-
<ex /> (Optional) Prove the pigeonhole principal (constructively, whithout the classical axiom).

-/

theorem pp {m n : ℕ} {f : Fin m → Fin n}
  : m > n → ∃ a b, a ≠ b ∧ f a = f b := sorry

/-
Exercise
===

<ex /> (Optional) Suppose we define the natural numbers as follows:
-/

def zero {α : Type u} : Set α := ∅
def one {α : Type u} : Set (Set α) := {zero}
def two {α : Type u} : Set (Set (Set α)) := {one}
-- etc.

/- How do you define the successor function? Addition? Etc? -/

--hide
end LeanW26
--unhide
