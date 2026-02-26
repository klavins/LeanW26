--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26



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
#check Nat.le               -- ≤ : ℕ → ℕ → Prop
#check List.lt              -- < : List α → List α → Prop (lexicographic)
#check Set.Subset           -- Set α → Set α → Prop

/- Lean's Connectives -/
#check And                  -- Prop → Prop → Prop
#check Or                   -- Prop → Prop → Prop

/- Equality -/
#check Eq                   -- Prop → Prop → Prop

/- Tail Equivalence on Sequences -/
def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n > m, σ₁ n = σ₂ n

/-
<div class='fn'>Tail equivalence is the same notion as <tt>EventuallyEq</tt>
in Mathlib's <a href="https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Defs.html#Filter.EventuallyEq">Filter Library</a>, except without the filters.</div>

-/

/-
Reflexivity
===
`R` is reflexive if `R x x` for all `x`.
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
`R` is symmetric if `R x y → R y x` for all `x` and `y`.
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
 `R` is antisymmetric if `R x y → R y x → x = y` for all `x` and `y`
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

example : Trans And := by
  intro p q r ⟨ hp, hq ⟩ ⟨ hq, hr ⟩
  exact ⟨ hp, hr ⟩

/- Inequality is not transitive, as you would expect. -/

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

<ex /> Show the symmetric closure of a symmetric relation is the relation itelf.

-/

example (R : α → α → Prop)
  : Symm R → ∀ x y, R x y ↔ (SymmC R) x y :=
  sorry

/-
<ex /> Show the symmetric closure of the reflexive closure is
the transitive closure of the reflexive closure.

-/

example (R : α → α → Prop) : ∀ x y,
  ReflC (TransC R) x y ↔ TransC (ReflC R) x y :=
  sorry


/-
Ordering
===

An **order relation** on a set `A` is a relation `A → A → Prop` that captures some notion of order.
A familiar example is the the `≤` relation on the natural numbers:

`≤` is an example of a **total order** on a set,
meaning any two elements `x` and `y` are related (i.e. `x≤y` or `y≤x`).

This need not be the case in general.
For example, the subset relation `⊆` on sets is only a
**partial order**, because one can find sets `A` and `B`
for which neither `A ⊆ B` or `B ⊆ A`.

Most of this material comes from the book
_Introduction to Lattices and Order_ by Davey and Priestly.

-/

/-
Partial Orders
===

A **partially ordered set** or **poset** is a set and a _less-than_ ordering relation
that is reflexive, anti-symmetric, and transitive. Using a new Lean `class`,
we define a class of types that have a less-than relation with these three properties. -/

class Poset (α : Type u) where
  le : α → α → Prop
  refl {x} : le x x
  anti_sym {x y} : le x y → le y x → x = y
  trans {x y z} : le x y → le y z → le x z

/-
Example : The Natural Numbers
===

We can assert `ℕ` is a `poset` by instantiating the `Poset` class as follows. -/

instance : Poset ℕ := ⟨
  Nat.le,
  Nat.le.refl,
  Nat.le_antisymm,
  Nat.le_trans
⟩

/- Conveniently, the proofs of each property already exist in Lean's library for `Nat`. -/

/-
Example : Sets
===

Similarly, Lean's standard library has all of these properties defined for sets.  -/

instance {A : Type u} : Poset (Set A) := ⟨
  Set.Subset,
  id,
  Set.Subset.antisymm,
  Set.Subset.trans
⟩

/-
Poset Notation
===

Instantiating the `LE` and `LT` classes in Lean's standard library allow
us to use `≤`, `≥`, `<`, and `≥` on elements of our `Poset` type.
-/

instance le_inst {A : Type u} [Poset A] : LE A := ⟨ Poset.le ⟩
instance lt_inst {A : Type u} [Poset A] : LT A := ⟨ fun x y => x ≤ y ∧ x ≠ y ⟩

example {A : Type u} [Poset A] (x : A) := x ≥ x

/-
Total Orders
===

A **total order** is a `Poset` with the added requirement that any two elements are comparable. -/

def Comparable {P : Type u} [Poset P] (x y : P) :=
  x ≤ y ∨ y ≤ x

class TotalOrder (T : Type u) extends Poset T where
  comp : ∀ x y : T, Comparable x y

/- **Example:** The natural numbers are a total order, which is shown via a
theorem in Lean's standard library: -/

instance nat_total_order : TotalOrder ℕ :=
  ⟨ Nat.le_total ⟩

/- **Example:**  Sets are not a total order, however. -/

example : ∃ x y : Set ℕ, ¬Comparable x y := by
  apply Exists.intro {1}
  apply Exists.intro {2}
  simp[Comparable]

/-
Exercises
===

<ex /> Given two sequences of natural numbers,
we define the *subsequence order* as follows.

First, note that strictly increasing function
can be specified with the Mathlib function

-/

#print StrictMono        -- fun f => ∀ a b, a < b → f a < f b

/- Then we define the ordering as -/

def subseq {α : Type u} (σ τ : ℕ → α) :=
  ∃ f, StrictMono f ∧ σ = τ ∘ f

/- Show subseq is a partial order on `ℕ → α` -/

instance {α : Type u} : Poset (ℕ → α) := {
  le := subseq,
  refl {σ} := sorry,
  anti_sym {σ τ}:= sorry,
  trans {σ τ ρ} := sorry
}

/-
<ex /> Is `subseq` a total order? Why or why not?

-/

/-
Semilattices
===

A (meet) *semilattice* is a `Poset` for which there exists a greatest
lower bound function, usually called `meet`, for every pair of
points `x` and `y`. Then we extend the hierarchy with a new class of orders. -/

class Semilattice (L : Type u) extends Poset L where
  meet : L → L → L
  lb : ∀ x y, meet x y ≤ x ∧ meet x y ≤ y
  greatest : ∀ x y w, w ≤ x → w ≤ y → w ≤ meet x y

/-
Example Semilattices
===

For example, the natural numbers form a semilattice.  -/

instance nat_semi_lattice : Semilattice ℕ :=
  ⟨
    Nat.min,
    by aesop,
    by aesop
  ⟩

/- So do sets. -/

instance set_semi_lattice {α : Type u}: Semilattice (Set α) :=
  ⟨
    (· ∩ ·),
    by aesop,
    by aesop
  ⟩

/-
Lattices
===

If all pairs of elements also have a least upper bound, then the `Poset` is called a *lattice*.
The least upper bound function is called the **join**. -/

class Lattice (L : Type u) extends Semilattice L where
  join : L → L → L
  ub : ∀ x y, (x ≤ join x y ∧ y ≤ join x y)
  least : ∀ x y w, x ≤ w → y ≤ w → join x y ≤ w

/-
Example Lattices
===
-/

/- Both ℕ and Sets are Lattices as well.
The join for ℕ is `Nat.max` and the join for sets is `Set.union`. -/

instance nat_lattice : Lattice ℕ :=
  ⟨
    Nat.max,
    by aesop,
    by aesop
  ⟩

instance set_lattice {α : Type u}: Lattice (Set α) :=
  ⟨
    (· ∪ ·),
    by aesop,
    by aesop
  ⟩

/-
Notation for Lattices
===

The meet and join of two elements `x` and `y` of a poset are
denonted `x ⊓ y` and `x ⊔ y`.
The notation classes for these operations are called `Min` and `Max`.
-/

instance Semilattice.and_inst {L : Type u} [Semilattice L] : Min L :=
  ⟨ meet ⟩

instance Lattice.or_inst {L : Type u} [Lattice L] : Max L :=
  ⟨ join ⟩

/- Now we can use meets and joins with types instantiating `Lattice`. -/

example : 3 ⊔ 4 = 4 := by decide

/-
Meet and Join Example Theorems
===

Here are two straightforward theorems about meets and joins
that test out the definitions and notation.
They follow from the definitions of greatest lower bound,
least upper bound, anti-symmetry, and reflexivity. -/

theorem Semilattice.meet_idempotent {L : Type u} [Semilattice L] (x : L) : x ⊓ x = x := by
  have ⟨ h1, h2 ⟩ := lb x x
  have h4 := greatest x x x Poset.refl Poset.refl
  exact Poset.anti_sym h1 h4

theorem Lattice.join_idempotent {L : Type u} [Lattice L] (x : L) : x ⊔ x = x := by
  have ⟨ h1, h2 ⟩ := ub x x
  have h4 := least x x x Poset.refl Poset.refl
  apply Poset.anti_sym h4 h1


/-
Exercise
===

<ex /> (Optional) A *complete semilattice* requires every set to have
a lower bound. A *complete lattice* requires every set to have an
upper bound.

-/

def IsLB {P : Type u} [Poset P] (S : Set P) (lb : P) := ∀ x ∈ S, lb ≤ x

class CompleteSemilattice (L : Type u) extends Poset L where
  inf : Set L → L
  lb : ∀ S, IsLB S (inf S)
  greatest : ∀ S w, (IsLB S w) → w ≤ inf S

def IsUB {P : Type u} [Poset P] (S : Set P) (ub : P) := ∀ x, x ∈ S → x ≤ ub

class CompleteLattice (L : Type u) extends CompleteSemilattice L where
  sup : Set L → L
  ub : ∀ S, IsUB S (sup S)
  least : ∀ S, ∀ w, (IsUB S w) → sup S ≤ w

/- Show that for any set `A` that `(A,⊆)` is a complete lattice by instantiating
the above classes. -/


/-
Exercise
===

<ex /> (Optional) In the definition of `inf` the condition `(IsLB S w)`
in  `(IsLB S w)→ w ≤ inf S` is trivially satisfied if `S = ∅`.
Therefore, `w ≤ inf ∅` for all `w`, meaning that `inf ∅`
is a top element. Similarly, `sup ∅` is a bottom element.
Conclude that every complete lattice is bounded.

 -/

@[simp]
def CompleteLattice.bot {L : Type u} [CompleteLattice L] : L :=
  sup (∅:Set L)

@[simp]
def CompleteLattice.top {L : Type u} [CompleteLattice L] : L :=
  CompleteSemilattice.inf (∅:Set L)

theorem CompleteLattice.is_bot {L : Type u} [CompleteLattice L]
  : ∀ x : L, bot ≤ x := sorry

theorem CompleteLattice.is_top {L : Type u} [CompleteLattice L]
  : ∀ x : L, x ≤ top := sorry



/-
Equivalence
===
An *equivalence relation* is reflexive, symmetric, and transitive.
Lean provides the following typeclass:
```lean
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  refl x : r x x
  symm {x y} : r x y → r y x
  trans {x y z} : r x y → r y z → r x z
```

Lean defines the typeclass
```lean
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r
```
to keep track of a relation, the type on which it operates, and to provide
notation. The requirement
`[Setoid α]` allows downstream declarations to require `α` to come equipped with
an equivalence relation.
 -/


/-
Equivalence Classes
===
An equivalence relation `≈ : α → α → Prop` partitions `α` into equivalence classes
of the form
```lean
{ y | x ≈ y }
```
Equivalences classes are disjoint:

-/

theorem disjoint_equiv {α : Type u} [s : Setoid α] {x₁ x₂ : α}
  : ¬ x₁ ≈ x₂ → { y | x₁ ≈ y } ∩ { y | x₂ ≈ y } = ∅ := by
  intro h
  ext z
  constructor
  · intro ⟨ h1 , h2 ⟩
    have := s.trans h1 (s.symm h2)
    exact h this
  · exact False.elim

/- And they partition the entire space -/

theorem univ_equiv {α : Type u} [s : Setoid α]
  : ⋃ x : α, {y|x≈y} = Set.univ := by
  ext z
  aesop


/-
Equivalence Preserving Functions
===

A function `f : α → α` *respects equivalence* if makes equivalent elements to equivalent elements.
-/

def respects {α : Type u} [Setoid α] (f : α → α) := ∀ x y,
  x ≈ y → f x ≈ f y

/-
A similar property may be stated for operations `op ∶ α → α → α`.
-/

def respects_op {α : Type u} [Setoid α] (op : α → α → α) := ∀ x₁ x₂ y₁ y₂,
  x₁ ≈ x₂ → y₁ ≈ y₂ → op x₁ y₁ ≈ op x₂ y₂

/- A respectful function respects equivalence classes. -/

theorem respects_ec {α : Type u} [Setoid α] {f : α → α} {x y : α}
  : respects f → f x ≈ y → f '' { z | z ≈ x } ⊆ { z | z ≈ y } := by
  intro hr hxy z ⟨ w, ⟨ h1, h2 ⟩ ⟩
  rw[←h2]
  exact Setoid.trans (hr w x h1) hxy

/- We can show a similar result for respectful operations. -/



/-
Equivalence
===

Many objects are defined up to equivalence:
- Rationals
- Cauchy Reals
- Integers `mod n`
- Lambda terms that reduce to the same value
- Equivalent states in an automaton
- Path equivalence in homotopy
- Quotient spaces in group theory, topology, ...

But there are issues:
- To reason about these objects you have to
    - reason about representatives of the equivalence classes
    - carry proofs with the representatives
    - extend to the whole equivalence class
- You can't use Lean's built-in definitional equality
on equivalence to do substitution, congruence, rewriting, etc.
- Equivalence classes are *sets* not *types*.

Lean provides a way to turn equivalences into equality
and equivalence classes into terms in a **quotient type**.


Quotients
===

Given a `Setoid` `S` the **quotient** of `S` is
_a new type_ `Quotient S`.

If `x:α` then
```
⟦x⟧ : Quotient S
```
is akin to the equivalence class of `x` under `≈`, but it is *not* a set.

Lean defines, axiomatically, the following:-/

#check Quotient.mk        -- A way to construct elements, also called **projection**
                          -- `(x : α) → Quotient S`, denoted `⟦x⟧`

#check Quotient.sound     -- An soundness axiom
                          -- `x ≈ y → ⟦x⟧ = ⟦y⟧

#check Quotient.lift     -- A way to lift functions
                         -- f → (∀ (a b : α), a ≈ b → f a = f b) → Quotient s → β

#check Quotient.lift_mk   -- The property that lifting respects ≈
                          -- Quotient.lift f h ⟦x⟧ = f x


/-
Example : Z2
===
-/

def M (x y : ℤ) : Prop := ∃ k, x - y = 2*k

instance m_equiv : Equivalence M := {
  refl x        := by use 0; simp,
  symm {x y}    := by intro ⟨ k, hm ⟩; use -k; linarith,
  trans {x y z} := by intro ⟨ k, hk ⟩ ⟨ j, hj ⟩; use (k+j); linarith
}

instance m_setoid : Setoid ℤ := ⟨ M, m_equiv ⟩

abbrev Z2 := Quotient m_setoid

instance m_zero : Zero Z2 := ⟨ ⟦0⟧ ⟩

/-
Z2: Lifting Unary Operators
===
Lifting a one argument function:
-/

def pre_neg (x : ℤ) : Z2 := ⟦-x⟧

theorem pre_neg_respects : ∀ (a b : ℤ), a ≈ b → pre_neg a = pre_neg b := by
  intro a b ⟨ k, hk ⟩
  apply Quotient.sound
  use -k
  linarith

def Z2.neg (X : Z2) : Z2 := Quotient.lift pre_neg pre_neg_respects X

instance z2_neg : Neg Z2 := ⟨ Z2.neg ⟩

#check -(⟦3⟧:Z2)

/-
Z2: Lifting Binary Operators
===
Lifting a two argument function:-/

def pre_add (x y : ℤ) : Z2 := ⟦x+y⟧

theorem pre_add_respects : ∀ (a₁ b₁ a₂ b₂ : ℤ),
  a₁ ≈ a₂ → b₁ ≈ b₂ → pre_add a₁ b₁ = pre_add a₂ b₂ := by
  intro a₁ b₁ a₂ b₂ ⟨k, hk⟩ ⟨j, hj⟩
  apply Quotient.sound
  use k+j
  linarith

def Z2.add (X Y : Z2) : Z2 := Quotient.lift₂ pre_add pre_add_respects X Y

instance Z2.hadd_inst : HAdd Z2 Z2 Z2 := ⟨ Z2.add ⟩
instance Z2.add_inst : Add Z2 := ⟨ Z2.add ⟩

/-
Z2 : Properties
===
-/

theorem Z2.zero_add (X : Z2) : 0 + X = X := by
  have ⟨ k, hm ⟩ := Quotient.exists_rep X
  rw[←hm]
  apply Quotient.sound
  use 0
  linarith

theorem Z2.neg_add_cancel (X : Z2) : -X + X = ⟦0⟧ := by
  have ⟨ k, hm ⟩ := Quotient.exists_rep X
  rw[←hm]
  apply Quotient.sound
  use 0
  linarith

theorem Z2.assoc (X Y Z : Z2) : X + Y + Z = X + (Y + Z) := by
  have ⟨ i, hi ⟩ := Quotient.exists_rep X
  have ⟨ j, hj ⟩ := Quotient.exists_rep Y
  have ⟨ k, hk ⟩ := Quotient.exists_rep Z
  rw[←hi,←hj,←hk]
  apply Quotient.sound
  use 0
  linarith


/-
Z2 is an Additive Group
===

Mathlib provides a function `AddGroup.ofLeftAxioms` to build a group instance. -/

instance Z2.group_inst : AddGroup Z2 :=
  AddGroup.ofLeftAxioms
  Z2.assoc Z2.zero_add Z2.neg_add_cancel

/- Everything true about groups is now easily proved for `Z2`: -/

example (X : Z2) : - -X = X := by group;

/-
Exercise
===
<ex /> (Optional) Show that the integers mod an positive number `m` form a group by
generalizing the construction for `Z2` above.

-/

/-
Tail Equivalence
===
Recall our definition of tail equilvalence:
```lean
def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n > m, σ₁ n = σ₂ n
```

We show `te` satisfies all the conditions of an equivalence relation:

-/

instance te_equiv {α : Type u} : Equivalence (te (α := α)) := {
  refl x := ⟨ 0, fun _ _ => rfl ⟩,
  symm {x y} := fun ⟨ m,h ⟩ => ⟨ m, by aesop ⟩,
  trans {x y z} := fun ⟨ m₁, h₁ ⟩ => fun ⟨ m₂, h₂ ⟩ => ⟨ m₁ ⊔ m₂, by aesop ⟩
}

instance te_setoid {α : Type u} : Setoid (ℕ → α) := {
  r := te,
  iseqv := te_equiv
}

/- Now we can write -/

--hide
section
--unhide

variable {α : Type u} (σ τ : ℕ → α)
#check σ ≈ τ

--hide
end
--unhide

/-
Germs
===

The quotient on the set of sequences under tail equivalence is called a `Germ`.
-/

def Germ (α : Type u) := Quotient (te_setoid (α := α))

/- We can construct elements of `Germ` using: -/

def Germ.mk {α : Type u} (σ : ℕ → α) := Quotient.mk te_setoid σ

def σ : ℕ → ℕ := fun x => 2*x

#check Germ.mk σ              -- Quotient te_setoid
#check (⟦σ⟧:Germ ℕ)            -- Quotient te_setoid


namespace Germ

instance inst_zero {α : Type u} [Zero α]: Zero (Germ α) := ⟨ ⟦fun _ => 0⟧ ⟩


/-
Germ Preoperators
===
-/

def pre_neg {α : Type u} [hn : Neg α] (σ : ℕ → α) : Germ α := ⟦fun n => -(σ n)⟧
def pre_add {α : Type u} [Add α] (σ τ : ℕ → α) : Germ α := ⟦fun n => σ n + τ n⟧

/- We can show `neg` preserves equivalence via: -/

theorem te_neg_respects {α : Type u} [Neg α]
  : ∀ (a b : ℕ → α), a ≈ b → pre_neg a = pre_neg b := by
  intro σ τ ⟨ m, h ⟩
  apply Quotient.sound
  use m
  aesop

theorem te_add_respects {α : Type u} [a : Add α] :
  ∀ (a₁ b₁ a₂ b₂ : ℕ → α), a₁ ≈ a₂ → b₁ ≈ b₂ → pre_add a₁ b₁ = pre_add a₂ b₂ := by
  intro a b c d ⟨ m1, h1 ⟩ ⟨ m2, h2 ⟩
  apply Quotient.sound
  use m1 ⊔ m2
  intro n hn
  aesop





/-
Germ Operators
===
We can lift functions from sequences to germs.
-/

def neg {α : Type u} [Neg α] : Germ α → Germ α :=
  Quotient.lift pre_neg te_neg_respects

def add {α : Type u} [Add α] : Germ α → Germ α → Germ α :=
  Quotient.lift₂ pre_add te_add_respects


/-
Exercises
===

<ex /> Show the shift operator

-/

def pre_shift {α : Type u} (σ : ℕ → α) : Germ α := ⟦fun n => σ (n+1)⟧

/- can be lifted to define an operator on `Germ`: -/

def shift {α : Type u} (σ : Germ α) : Germ α :=
  Quotient.lift pre_shift sorry σ

/- <ex /> Show

-/

example : shift (0:Germ ℤ) = 0 := sorry


/-
<ex /> What is an example of a function `f` on `ℕ → ℕ` that does not preservce equivalence? Show:

-/

def my_func (σ : ℕ → ℕ) : ℕ → ℕ := sorry
def σ₁ : ℕ → ℕ := sorry
def σ₂ : ℕ → ℕ  := sorry
example : σ₁ ≈ σ₂ ∧ ¬ my_func σ₁ ≈ my_func σ₂ := sorry


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
  | assoc {a b c}      : eq ((a+b)+c) (a+(b+c))
  | comm {a b}         : eq (a+b) (b+a)
  | add_zero_right {a} : eq (a+zero) a
  | add_zero_left {a}  : eq (zero+a) a

  -- Congruence
  | congr {a b c d}    : eq a c → eq b d → eq (a+b) (c+d)

  -- Closures
  | refl {a}           : eq a a
  | symm {a b}         : eq a b → eq b a
  | trans {a b c }     : eq a b → eq b c → eq a c

/- Think of these rules as defining a proof theory for showing when two expressions are equal. -/

namespace Expr

/-
Instances
===
Since the definition of `~` includes reflexivity, symmetry, and transitivity, it is easy to show
it is an equivalence relation.
-/

instance inst_equiv : Equivalence Expr.eq := ⟨ @eq.refl, eq.symm, eq.trans ⟩

instance inst_setoid : Setoid Expr := ⟨ Expr.eq, inst_equiv ⟩

/- Now we can write simple examples: -/

example : (one+zero)+one ≈ one+one := by
  apply eq.congr
  · apply eq.add_zero_right
  · apply eq.refl

/-
Congruence
===
We can build out everything you would expect to see in a rewriting system.
-/

theorem cong_left {a b c : Expr} : a ≈ b → a + c ≈ b + c := by
  intro h
  exact eq.congr h eq.refl

theorem cong_right {a b c : Expr} : b ≈ c → a + b ≈ a + c := eq.congr eq.refl

theorem cong_assoc_left {a b c a' b' : Expr}
  : a ≈ a' → b ≈ b' → (a + b) + c ≈ (a' + b') + c := by
  intro ha hb
  apply cong_left
  exact Expr.eq.congr ha hb

theorem cong_assoc_right {a b c b' c' : Expr}
  : b ≈ b' → c ≈ c' → a + (b + c) ≈ a + (b' + c') := by
  intro hb hc
  apply cong_right
  apply Expr.eq.congr hb hc

theorem sub {a b c : Expr} : a ≈ c → b ≈ c → a ≈ b := by
  intro h1 h2
  exact eq.trans h1 (eq.symm h2)


/-
Soundness
===
We need to make sure we do not accidentlly
say two expressions are equal if they do not evaluate to the same thing.
To check this we define an eval function:
-/

def eval : Expr → Nat
  | .zero => 0
  | .one => 1
  | .add a b => eval a + eval b

/- We can check soundess by induction on the equivalence: -/

theorem sound (e f : Expr) : e ≈ f → eval e = eval f := by
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

<ex /> (Optional) Show that equivalence on `Expr` is complete:

-/

theorem complete {e f : Expr} : eval e = eval f → e ≈ f := sorry

/-
One way to do this is to define a normal form `(1+(1+(1+0)))` for each
`Expr`, establish completness for normal forms as a `lemma`, and then
use transitivity to establish the desired result.
-/

/-
<ex /> (Optional) Define

-/

def E := Quotient Expr.inst_setoid

/- and show -/

def E_equiv_Nat : E ≃ ℕ := sorry

--hide
end Expr
end Germ
end LeanW26
--unhide
