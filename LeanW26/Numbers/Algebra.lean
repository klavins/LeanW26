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

--notdone

/-
Algebra
===
-/

/-
Overview
===

- Groups
- Monoids
- Rings
- Fields

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
Building the Theory
===

Group theory is a huge topic dating back to the 18th centyr.
It is well beyond the scope of this course to prove much about it.

In a textbook, one usually does builds up simple identities (such as `- - x = x`)
and uses those to prove more complex identities. The order in which these
identities are proved is an example of code reuse! We will give a few examples.

Historically, the application of proof assistants to Group Theory were
early successes.

For example:

- Rideu and Théry, "Formalising Sylow’s theorems in Coq", 2006. [🔗](https://arxiv.org/pdf/cs/0611057). Also appears in Mathlib [🔗](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html).

- Gontheir et al, "A Machine-Checked Proof of the Odd Order Theorem", ITP 2013.
[🔗](https://www.cs.unibo.it/~asperti/PAPERS/odd_order.pdf). Original proof is 255 pages long.


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

The group operation can either be like addition or like multiplication,
depending on the sample. For our purposes we'll assume our operation is
like `+`.


-/

infixl:60 " + " => Group.op            -- left associating infix syntax
prefix:95 "-" => Group.inv

/- Now we have standard notation. Note that we can declare a type `G`
to be a group by using the notation [Group G]. -/

open Group CommGroup

variable (G : Type) [Group G] (a b : G)
#check -(a + b) + a           -- G
#check a + b + e              -- G


/- Mathlib defines both `Group` and `AddGroup`. They are identical
mathematically, but have different notation associated with them. -/




/-
Group Theorems and Identites
===

In the standard textbook development of group theory, one builds out
all the various identities from the axioms. For example,
-/

--hide
open Group
variable {G : Type u} [Group G] {a b c : G}
--unhide

theorem Group.id_inv_left : e + (-a) = -a := id_left (a := -a)

/- From which you can prove. -/

lemma cancel_left : a + b = a + c → b = c := by
  intro h
  apply congrArg (fun t => -a + t) at h  -- -a + (a + b) = -a + (a + c)
  rw[←assoc] at h                        --   -a + a + b = -a + (a + c)
  rw[inv_left] at h                      --        e + b = -a + (a + c)
  rw[id_left] at h                       --            b = -a + (a + c)
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

theorem id_right : a + e = a := by
  apply cancel_left (a := -a)
  calc  -a +  (a + e)
  _   = (-a + a) + e := by rw[assoc]
  _   = (e + e : G)    := by rw[inv_left]
  _   = e              := by rw[id_left]
  _   = -a + a       := by rw[inv_left]

/- which can be done with simp as well. You have to tell simp which way to associate.  -/

example : a + e = a := by
  apply cancel_left (a := -a)
  simp[←assoc,id_left,inv_left]

/-
Proving inv_right
===

We can also show `inv_right` is derivable. -/

theorem inv_right : a + (-a) = e := by
  apply cancel_left (a := -a)
  calc  -a + (a + (-a))
  _   = (-a + a) + (-a) := by rw[assoc]
  _   = e + (-a)         := by rw[inv_left]
  _   = -a             := by rw[id_left]
  _   = -a + e         := by rw[id_right (a := -a)]

/-
These can also be done as a `simp` proof.
-/


/-
Exercise
===

<ex /> Show the identity of a group is unique

-/

theorem id_unique {e' : G} : (∀ a, e'+ a = a) → e = e' := by sorry

/- Hints:
- Introduce the hypothesis
- Using a `have`, establish `e' + e = e'` via a group property
- Using another `have`, establish `e' + e = e` via our hypothesis
- Use these intermediate results to rewrite the goal.
-/

/-
<ex /> Show that the inverse of every element is unique. The proof goes like this:
- Suppose `b + a = e` and `c + a = e`
- Then

```lean
b = b + e = b + (a + c) = (b + a) + c = e + c = c .
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
  comm {a b}    := by cases a <;> simp[op] <;> aesop
}

/- You could also instantiate `Monoid`, `Group` and `CommGroup` sequentially,
only adding new fields each time. Or, -/

instance Spin.inst_group : Group Spin := inferInstance

/-
Group Theorems apply to the Spin Group
===
-/

example {x : Spin} : x + e = x := by simp[id_right]

open Spin in
example : up + up = up := by
  have : up = -up := rfl
  nth_rewrite 1 [this]       -- -up + up = up
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
However, multiplication is not required to have inverses.

To build a `Ring` type we first define a `Monoid` type for multiplication.
-/

class Monoid (M : Type u) where
  mul : M → M → M
  one : M
  mul_assoc {a b c : M} : mul (mul a b) c = mul a (mul b c)
  mul_id_left {a : M}   : mul one a = a
  mul_id_right {a : M}  : mul a one = a

/- We cannot derive `mul_id_right` as we did with `Group`,
because we do not have inverses.  -/

/-
Rings
===
Now we have what we need do define a Ring.
-/

class Ring (R : Type u) extends CommGroup R, Monoid R where
  left_distrib {x y z : R}  : mul x (op y z) = op (mul x y) (mul x z)
  right_distrib {x y z : R} : mul (op y z) x = op (mul y x) (mul z x)

/-
Ring Notation
===
-/

variable {R : Type u} [Ring R]

infixl:80 " * " => Monoid.mul

def Group.sub (x y : R):= Group.op x (-y)
infixl:60 " - " => Group.sub

open Monoid Ring

section
  variable (x y z : R)
  #check x * (y + z) - x    -- R
end section

/-
Operating on Equations
===

When proving `Ring` identites, it is useful to operate on both sides
of an equation. That is, we may want to change the proof from

```lean
h : y = z
⊢ ...
```

to

```lean
h : x + y = z + y
⊢ ...
```

We can do this with theorems of the form:

-/
--hide
variable {x y z : R}
--unhide

theorem Ring.add_left  (h : y = z) (x : R) : x + y = x + z := by rw[h]
theorem Ring.add_right (h : y = z) (x : R) : y + x = z + x := by rw [h]
theorem Ring.mul_left  (h : y = z) (x : R) : x * y = x * z := by rw [h]
theorem Ring.mul_right (h : y = z) (x : R) : y * x = z * x := by rw [h]


/-
Example Identity
===
-/
theorem mul_zero : x * e = e := by

  have h := left_distrib (x := x) (y := e) (z := e)
                      -- x*(e + e) = x*e + x*e

  have h := Ring.add_left h (-(x*e))
                     -- -(x*e) + x*(e + e) = -(x*e) + (x*e + x*e)

  rw[id_left]  at h  -- -(x*e) + x*e = -(x*e) + (x*e + x*e)
  rw[inv_left] at h  -- e = -(x*e) + (x*e + x*e)
  rw[←assoc]   at h  -- e = -(x*e) + x*e + x*e
  rw[inv_left] at h  -- e = e + x*e
  rw[id_left]  at h  -- x*e = e

  exact h.symm


/- The `rw` part can be replaced with `simp only [id_left,inv_left,←assoc] at h`-/

/-
Another Example
===
-/

theorem neg_one : (-one:R)*(-one:R) = one := by sorry


theorem inv_to_mul : -x = (-e:R) * x := by
  have h1 : x + (-x) = e := by rw[inv_right]

  sorry

theorem neg_mul : (-x) * (-y) = x*y := by

  sorry


/-
Exercise
===

<ex /> Todo

-/


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


/-
Nontrivial Types
===

Our next goal is to define **fields**.
Typically, we also require that a field `F` is not simply `{0}`.

To prevent trivial
situations like this, we define

```lean
class Nontrivial (α : Type*) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y
```

Which allows us to do:

```lean
obtain ⟨ x, y, hxy ⟩ := (inferInstance : Nontrivial F).exists_pair_ne
```

in a proof to get a context with
```lean
x : F
y : F
hxy : x ≠ y
```
-/

/-
Fields
===
A **Field** is a commutative ring with inverses for all elements except zero.
-/

class Field (F : Type u) extends Ring F, Nontrivial F where
  minv : F → F
  minv_zero : minv e = e
  mul_inv_prop {x : F} : x ≠ e → mul x (minv x) = one
  mul_comm {x y : F} : mul x y = mul y x

open Field

variable {F : Type u} [Field F] {x y z : F}

/- The convention 0⁻¹ = 0 is a convention that makes proof automation easier. -/

/-
Field Notation
===

We reuse the notation from Groups and Rings, adding just
-/

postfix:95 "⁻¹" => Field.minv

/- for the field inverse.

Now we can write

-/

section
  variable (x y : F)
  #check one * (x - x⁻¹) + e * y
end section

/- for example. -/

/-
Example Field Identities
===

We only put `one * x = x` in our definition because we can prove the symmetric case:

-/

theorem mul_id_right : x * one = x := by
  rw[Field.mul_comm]
  rw[mul_id_left]

/- Other basic theorems include -/

theorem neg_inv : (-x)⁻¹ = -(x⁻¹) := by
  sorry

/-
A Proof that 1 ≠ 0
===
-/

theorem one_ne_e : (one:F) ≠ e := by

  intro h

  obtain ⟨ x, y, hxy ⟩ := (inferInstance : Nontrivial F).exists_pair_ne

  have hx : x = e := by
    calc
      x = x * one := by rw[mul_id_right]
      _ = x * e   := by rw[h]
      _ = e       := by rw [mul_zero]

  have hy : y = e := by
    calc
      y = y * one := by rw[mul_id_right]
      _ = y * e   := by rw[h]
      _ = e       := by rw[mul_zero]

  exact hxy (hx.trans hy.symm)

@[simp]
theorem one_inv : (one:F)⁻¹ = one := by
  have h : one = (one:F) * one⁻¹ := by rw[mul_inv_prop one_ne_e]
  nth_rewrite 2 [h]
  rw[mul_id_left]


--hide
end
end
--unhide
