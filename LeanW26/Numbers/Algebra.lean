import mathlib

namespace LeanW26

set_option linter.style.emptyLine false
set_option linter.style.commandStart false

--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.



/-
Algebra
===
-/

/-
Groups
===

A **Group** is a set `G` along with a binary operation `∘` having the following properties:
- Associativity : `(a ∘ b) ∘ c = a ∘ (b ∘ c)` for all `a`, `b`, and `c`
- Identity Element: There is an element `e` such that `a ∘ e = a` for all `a`
- Inverses: Every element `a` has an inverse `a⁻¹` such that `a ∘ a⁻¹ = e`

A **Monoid** is a group without inverses.

A **Commutative Group** is a group where `a ∘ b = b ∘ a` for all `a` and `b`.

Many mathematical objects are groups: ℤ, ℚ, ℝ, ℂ with `+` or `*`. Matrices, polynomials,
functions, permutations, cycles, symmetries, paths, etc.

Ideally, a proof assistant can reason at an abstract level about groups in general,
so results about groups can be reused for any concrete group.

Lean does this with *type classes* and *instances*.

-/

/-
Preliminaries
===

We will be redefining these structures, using the same names as Mathlib does.
So we'll put everything into a temporary namespace.

-/

namespace Temp                       -- avoid name conflict with Mathlib

/-
And we need a universe
-/

universe u

/-
Note that Mathlib defines Groups and other algebraic structures in a considerably more
sophisticated way than we do here, although it uses similar typeclasses. The goal with
Mathlib is to build a general proof-checking environment, not to teach formaliziation.

Hopefully these slides teach the basic approach. Actual projects should use Mathlib's
typeclasses.

-/


/-
A Group Class
===

You can put all of the properties of a group into a type class, starting with a base `Monoid` class.
-/



class Group (G : Type u) where
  op : G → G → G
  e : G
  assoc {a b c} : op (op a b) c = op a (op b c)
  id_left {a} : op e a = a
  inv : G → G
  inv_left {a} : op (inv a) a = e

/- And extend `Group` to the special case of a commutative (or abelian) group: -/

class CommGroup (G : Type u) extends Group G where
  comm {a b} : op a b = op b a



/-
Group Notation
===

We add standard notation for `Group` using the following.
Lean uses `∘` for function composition, so we can't easily
reuse it. In Mathlib, one usually uses `*`.
Here, we'll use `•` (written `\bu`), because, well, I like it.

-/

infixl:60 " • " => Group.op            -- left associating infix syntax
postfix:100 " ⁻¹ " => Group.inv

/- Now we have standard notation. Note that we can declare a type `G`
to be a group by using the notation [Group G]. -/

open Group CommGroup

section
  variable (G : Type) [Group G] (a b : G)
  #check (a • b)⁻¹ • a
  #check a • b • e
end

/-
Group Theorems
===

In the standard textbook development of group theory, one builds out
all the various identities from the axioms. For example,
-/

--hide
open Group
variable {G : Type u} [Group G] {a b c : G}
--unhide

theorem Group.id_inv_left : e • a⁻¹ = a⁻¹ := id_left (a := a⁻¹)

/- From which you can prove. -/

lemma cancel_left : a • b = a • c → b = c := by
  intro h
  apply congrArg (fun t => a⁻¹ • t) at h -- a⁻¹ • (a • b) = a⁻¹ • (a • c)
  rw[←assoc] at h                        -- (a⁻¹ • a) • b = a⁻¹ • (a • c)
  rw[inv_left] at h                      --         e • b = a⁻¹ • (a • c)
  rw[id_left] at h                       --             b = a⁻¹ • (a • c)
  rw[←assoc] at h                        -- etc
  rw[inv_left] at h
  rw[id_left] at h
  exact h

/- Or you can write `simp_all only [←assoc,inv_left,id_left]`. -/

/-
Calculation Style Proofs
===

You can also do proofs using the `calc` tactic, which shows the logic you
are applying very clearly.

For example, we can show `id_right` is derivable.
-/

theorem id_right : a • e = a := by
  apply cancel_left (a := a⁻¹)
  calc  a ⁻¹ • (a • e)
  _   = (a ⁻¹ • a) • e := by rw[assoc]
  _   = (e • e : G)    := by rw[inv_left]
  _   = e              := by rw[id_left]
  _   = a ⁻¹ • a       := by rw[inv_left]

/- which can be done with simp as well. You have to tell simp which way to associate.  -/

example : a • e = a := by
  apply cancel_left (a := a⁻¹)
  simp[←assoc,id_left,inv_left]

/-
Another proof
===

We can also show `inv_right` is derivable. -/

theorem inv_right : a • a⁻¹ = e := by
  apply cancel_left (a := a⁻¹)
  calc  a⁻¹ • (a • a⁻¹)
  _   = (a⁻¹ • a) • a⁻¹ := by rw[assoc]
  _   = e • a⁻¹         := by rw[inv_left]
  _   = a⁻¹             := by rw[id_left]
  _   = a⁻¹ • e         := by rw[id_right (a := a⁻¹)]

/-
These can also be done as a `simp` proof.
-/

/-
Exercise
===

<ex /> Show the identity of a group is unique

-/

theorem id_unique {e' : G} : (∀ a, e' • a = a) → e = e' := by sorry

/- Hints:
- Introduce the hypothesis
- Using a `have`, establish `e' • e = e'` via a group property
- Using another `have`, establish `e' • e = e` via our hypothesis
- Use these intermediate results to rewrite the goal.
-/

/-
<ex /> Show that the inverse of every element is unique. The proof goes like this:
- Suppose `b • a = e` and `c ∘ a = e`
- Then

```lean
b = b • e = b • (a • c) = (b • a) • c = e • c = c .
```

-/

/-
Spin Again
===

Recall the definition of a `Spin` from the notes on `Equality`.
-/

inductive Spin where | up | dn

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

open Spin in
def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

/- `Spin` is a group where `up` is the identity and each element is its own inverse.

<div class='fn'>Generally speaking, the spin group Spin(n) is a Lie group
that serves as the double cover of the special orthogonal group SO(n) and
describes the symmetries of fermions (like electrons) in quantum mechanics.
Spin(1) is the group with just two elements.

-/

/-
Instantiating Spin as a Group
===

We can instantiate `Spin` as a `Group` by simply filling in all the fields: -/

open Spin in
instance Spin.inst_comm_group : CommGroup Spin := {
  op := op,
  e := up,
  inv := id,
  assoc {a b c} := by cases a <;> cases b <;> cases c <;> aesop,
  id_left {a}   := by cases a <;> aesop
  inv_left {a}  := by cases a <;> aesop
  comm {a b} := by cases a <;> simp[op] <;> aesop
}

/- You could also instantiate `Monoid`, `Group` and `CommGroup` sequentially,
only adding new fields each time. Or, -/

instance Spin.inst_group : Group Spin := inferInstance

/-
Group Theorems apply to the Spin Group
===
-/

example {x : Spin} : x • e = x := by simp[id_right]

open Spin in
example : up • up = up := by
  have : up = up⁻¹ := rfl
  nth_rewrite 1 [this]       -- up ⁻¹ • up = up
  rw[inv_left]               -- e = up
  rfl

/-
Exercises
===

<ex /> Todo

-/

/-
Monoids
===

A **Ring** is *almost* two groups, one for addition and one for multiplication,
along with distributivity.
However, multiplication is not required to have inverses. To build a `Ring` type
we first define a `Monoid` type for multiplication.
-/

class Monoid (M : Type u) where
  mul : M → M → M
  one : M
  mul_assoc {a b c : M} : mul (mul a b) c = mul a (mul b c)
  mul_id_left {a : M} : mul one a = a
  mul_id_right {a : M} : mul a one = a

/-
Rings
===
Now we have what we need do define a Ring.
-/

class Ring (R : Type u) extends CommGroup R, Monoid R where
  left_distrib {x y z : R} : mul x (op y z) = op (mul x y) (mul x z)
  right_distrib {x y z : R} : mul (op y z) x = op (mul y x) (mul z x)

/- And standard notation: -/

variable {R : Type u} [Ring R] (x y z : R)

infixl:60 " + " => Group.op
infixl:80 " * " => Monoid.mul
prefix:95 " - " => Group.inv

def Group.sub := Group.op x (-y)

infixl:60 " - " => Group.sub

open Monoid Ring

section
  #check x*(y+z)⁻¹ -x
end

/-
An Example Ring Theorem
===
-/

theorem e_plus_e : (e + e : R) = e := by rw[id_left]

theorem mul_zero : x * e = e := by

  have h := left_distrib (x := x) (y := e) (z := e)
    -- h : x * (e + e) = x * e + x * e

  have h := congrArg (fun t => (x*e)⁻¹ + t) h
  simp only at h
    -- h : -(x * e) + x * (e + e) = -(x * e) + (x * e + x * e)

  rw[e_plus_e] at h  -- -(x * e) + x * e = -(x * e) + (x * e + x * e)
  rw[inv_left] at h  -- e = -(x * e) + (x * e + x * e)
  rw[←assoc]   at h  -- e = -(x * e) + x * e + x * e
  rw[inv_left] at h  -- e = e + x * e
  rw[id_left]  at h  -- x * e = e

  exact h.symm


/-
Spin is a Monoid
===

First we definition multiplication for `Spin`.
-/

def Spin.mul (a b : Spin) : Spin :=
  match a, b with
  | dn, dn => dn
  | _, _ => up

/- And then we can create the `Monoid` instance. -/

instance Spin.inst_monoid : Monoid Spin := {
  one := dn,
  mul := Spin.mul
  mul_assoc {x y z} := by cases x <;> cases y <;> cases z <;> aesop
  mul_id_left {x}   := by cases x <;> simp[Spin.mul]
  mul_id_right {x}  := by cases x <;> simp[Spin.mul]
}

/-
Spin is a Ring
===
-/

instance Spin.inst_ring : Ring Spin := {
  left_distrib {x y z} := by cases x <;> cases y <;> cases z <;> aesop
  right_distrib {x y z} := by cases x <;> cases y <;> cases z <;> aesop
}



--hide
end Temp
end LeanW26
--unhide
