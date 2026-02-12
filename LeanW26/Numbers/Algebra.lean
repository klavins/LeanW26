import mathlib.tactic

namespace LeanW26

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

#eval Lean.versionString

--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

/-
Algebra
===
Don't reinvent the wheel (unless you really want to understand wheels).
-/

/-
Overview
===

A mathematical theory can be built up from definitions and their properties.

We use typeclasses of the form:

```lean
class MyClass extends A, B, C where
  -- data
  x : α
  y : β
  ...
  -- properties
  h₁ : ...
  h₂ : ...
```
creating a hierarchy in which any object of type  `MyClass` is also an object of
types `A`, `B` and `C`. Properties have the form

```lean
theorem my_theorem {α : Type u} [MyClass α] {x y z : α} : P x y z := ...
```

Example Typeclass Hierarchies
===

- A `Field` is built from a `Ring`, which is built from a `Monoid` and a `Group` (today)
- An `Automaton` is built from `Graph` and an `IO` relation
- A `MetricSpace` is built from a `PsuedometricSpace` and a `DistanceFunction`
- A `CartesianClosedCategory` is built from a `Category` with `HasProducts` and `HasExponentials`.

It is 100% worth rebuilding these edifices from scratch, even though they are
defined in Mathlib (and in other proof assistants like Agda, Rocq, Isabelle, etc.).

So, with the aim of learning *how* to formalize, we rebuild some of the very basic
foundations of modern algebra. Hopefully this will help you use Mathlib, which is
built using similar principle.

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

Many mathematical objects are groups: ℤ, ℚ, ℝ, ℂ. Matrices, polynomials,
functions, permutations, cycles, symmetries, paths, etc.

Ideally, a proof assistant can reason at an abstract
level about groups in general, so results about groups
can be reused for any concrete group.

Lean does this with *type classes* and *instances*.

-/

/-
Building the Theory
===

Group theory is a huge topic, well beyond the scope of this course and
advanced results require more infrastrcture than presented here, but much of
it is available in Mathlib.

Historically, the application of proof assistants to Group Theory were
some of the early successes of the technology.

For example:

- Rideu and Théry, "Formalising Sylow’s theorems in Coq", 2006. [(link)](https://arxiv.org/pdf/cs/0611057). Also appears in Mathlib [(link)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html).

- Gontheir et al, "A Machine-Checked Proof of the Odd Order Theorem", ITP 2013.
[(link)](https://www.cs.unibo.it/~asperti/PAPERS/odd_order.pdf). Original proof is 255 pages long.

- ...

-/

/-
Preliminaries
===

We will redefine Mathlib's basic typeclasses for Group, Ring, etc.,
using the same names as Mathlib uses.
So we'll put everything into a temporary namespace.

-/

namespace Temp                       -- avoid name conflict with Mathlib

/-
And we need a universe
-/

universe u

/-
Mathlib defines Groups and other algebraic structures in a considerably more
sophisticated way than we do here, although it uses similar typeclasses. The goal with
Mathlib is to build a general proof-checking environment, not to teach formaliziation.

Actual abstract algebra projects should use Mathlib's typeclasses.

-/


/-
A Group Class
===

You the properties of a group into a typeclass.
-/

class Group (G : Type u) where
  op : G → G → G                                    -- data
  e : G
  assoc {a b c} : op (op a b) c = op a (op b c)     -- properties
  id_left {a} : op e a = a
  inv : G → G
  inv_left {a} : op (inv a) a = e

/- And extend `Group` to the special case of a commutative (or abelian) group: -/

class CommGroup (G : Type u) extends Group G where
  comm {a b} : op a b = op b a                      -- additional property

/-
Any theorem we prove about a `CommGroup` is also true about a `Group`.
-/

/-
Group Notation
===

The group operation can either be like addition or like multiplication,
depending on the application. We'll assume our operation is
like `+`.

-/

infixl:60 " + " => Group.op            -- left associating infix syntax
prefix:95 "-" => Group.inv

/- Now we have standard notation.  -/

open Group CommGroup

variable (G : Type u) [Group G] (a b : G)
#check -(a + b) + a           -- G
#check a + b + e              -- G


/- We open the `Group` so we can write `e` and `op` instead of `Group.e`
and `Group.op`. -/

open Group

/-
Group Theorems and Identites
===

In the standard textbook development of group theory, one builds out
all the various identities from the axioms.

For example, we can show a variant of `id_left` for inverses.
-/

theorem Group.id_inv_left {G : Type u} [Group G] {a : G}
  : e + (-a) = -a
  := by rw[id_left]

/-
The variable declarations become
extremely repetetive and clutter the code, making it harder to read. Therefore,
we delare variables for all of our subsequent `Group` theorems ahead of time with
-/

variable {G : Type u} [Group G] {a b c : G}

/- Theorem statements then look simple: -/

theorem Group.id_plus_id : (e:G) + e = e
  := by rw[id_left]


/-
Cancelation Theorem
===

We prove a few identities to show a sense of the process.

A super useful property for proving identities is:

-/

theorem Group.cancel_left : a + b = a + c → b = c := by
  intro h
  apply congrArg (fun t => -a + t) at h
  rw[←assoc] at h
  rw[inv_left] at h
  rw[id_left] at h
  rw[←assoc] at h
  rw[inv_left] at h
  rw[id_left] at h
  exact h

/- Or you can write `simp_all only [←assoc,inv_left,id_left]`. -/

/-
Calculation Style Proofs
===

You can do proofs using the `calc` tactic, which shows the logic you
are applying very clearly.

For example, we can show `id_right` is derivable.
-/

theorem Group.id_right : a + e = a := by
  apply cancel_left (a := -a)
  calc  -a +  (a + e)
  _   = (-a + a) + e   := by rw[assoc]
  _   = (e + e : G)    := by rw[inv_left]
  _   = e              := by rw[id_left]
  _   = -a + a         := by rw[inv_left]

/- which can be done with `simp` as well. You just have to tell `simp` which way to associate.  -/

example : a + e = a := by
  apply cancel_left (a := -a)
  simp[←assoc,id_left,inv_left]

/-
Proving inv_right
===

We can also show `inv_right` is derivable. -/

theorem Group.inv_right : a + (-a) = e := by
  apply cancel_left (a := -a)
  calc  -a + (a + (-a))
  _   = (-a + a) + (-a) := by rw[assoc]
  _   = e + (-a)        := by rw[inv_left]
  _   = -a              := by rw[id_left]
  _   = -a + e          := by rw[id_right (a := -a)]

/-
which can also be done as a `simp` proof.
-/


/-
Exercises
===

<ex /> Show the identity of a group is unique

-/

theorem Group.id_unique {e' : G} : (∀ a, e'+ a = a) → e = e' := by sorry

/- Hints:
- Introduce the hypothesis
- Using a `have`, establish `e' + e = e'` via a group property
- Using another `have`, establish `e' + e = e` via our hypothesis
- Use these intermediate results to rewrite the goal.
-/

/-
<ex /> Show that the inverse of every element is unique:

-/

theorem Group.inv_unique : b + a = e → c + a = e → b = c := sorry

/-
A `calc` proof goes like this:
```lean
b = b + e = b + (a + c) = (b + a) + c = e + c = c
```
-/

/-
Spin Again
===

Recall the definition of a `Spin` from the notes on `Equality`.
-/

inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

/-

<div class='fn'>Generally speaking, the spin group Spin(n) is a Lie group
that serves as the double cover of the special orthogonal group SO(n) and
describes the symmetries of fermions (like electrons) in quantum mechanics.
Spin(1) is the group with just two elements.

-/

/-
Instantiating Spin as a Group
===

`Spin` is a group where `up` is the identity and each element is its own inverse.
-/

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
only adding new fields each time.

Or do -/

instance Spin.inst_group : Group Spin := inferInstance

/-
Group Theorems apply to the Spin Group
===

With the instantiation of `Spin` as a `CommGroup`, we can do
-/

example (x : Spin) : x + up = x := by exact id_right
example : up + up = up := by exact id_plus_id
example : up + dn = dn + up := by exact comm

/- For example. -/

/-
Exercise
===

<ex /> Show the product of two groups is a group by completing
the following instance.

-/

instance Group.prod {G H : Type u} [Group G] [Group H] : Group (G × H) := {
  op x y := (x.1 + y.1, x.2 + y.2),
  e := (e,e),
  inv x := (-x.1, -x.2),
  id_left {x} := by simp[id_left]
  inv_left := by simp[inv_left],
  assoc :=  by simp[assoc]
}

infix:50 " × " => Group.prod

/-
<ex /> Show

-/

example : e = (up,up) := sorry
example : -(up,up) = (up,up):= sorry
example (x : Spin × Spin) : - x + x = (up,up) := sorry

/-

-/

/-
Ring Theory
===

The primary example of a **Commutative Ring** is the integers `ℤ`, which have:
- 0 and 1
- associative and commutative addition and additive inverses
- associative and commutative multiplication, but no multiplicative inverses

Other rings include:
- Polynomial rings
- Quotient rings
- Continuous functions on a topological space
- Power series
- Algebraic numbers


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
Now we have what we need do define a `Ring`.
-/

class Ring (R : Type u)
  extends CommGroup R, Monoid R where
  l_distrib {x y z : R} : mul x (op y z) = op (mul x y) (mul x z)
  r_distrib {x y z : R} : mul (op y z) x = op (mul y x) (mul z x)

class CommRing (R : Type u)
   extends Ring R where
   mulcomm {x y : R} : mul x y = mul y x

/-
Ring Notation
===

As we did for groups, we define notation.
-/

variable {R : Type u} [CommRing R]

infixl:80 " * " => Monoid.mul

def Group.sub (x y : R):= Group.op x (-y)
infixl:60 " - " => Group.sub

open Monoid Ring CommRing

/- The result looks like the integers, which is nice. -/

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

theorem Ring.add_left  (h : y = z) (x : R) : x + y = x + z := by rw [h]
theorem Ring.add_right (h : y = z) (x : R) : y + x = z + x := by rw [h]
theorem Ring.mul_left  (h : y = z) (x : R) : x * y = x * z := by rw [h]
theorem Ring.mul_right (h : y = z) (x : R) : y * x = z * x := by rw [h]


/-
Example Identity
===
-/
theorem mul_zero : x * e = e := by
  have h0 := l_distrib (x := x) (y := e) (z := e)
  have h := Ring.add_left h0 (-(x*e))
  rw[id_left]  at h
  rw[inv_left] at h
  rw[←assoc]   at h
  rw[inv_left] at h
  rw[id_left]  at h
  exact h.symm


/- The `rw` part can be replaced with `simp only [id_left,inv_left,←assoc] at h`-/

/-
Others Examples
===
-/

theorem neg_one : (-one:R)*x = -x := by

  have h0 : (one:R) + -(one:R) = (e:R) := by rw[inv_right]

  have h1 : e = (e:R) * x := by rw[mulcomm,mul_zero]

  nth_rewrite 2 [←h0] at h1
  rw[r_distrib,mul_id_left] at h1

  have h2 := add_left h1 (-x)
  rw[←assoc,id_right,inv_left,id_left] at h2

  exact h2.symm



/-
Exercise
===

<ex /> Show

-/

theorem factor_mul_inv_right : x*(-y) = -(x*y) := sorry

/-

One way to prove this identity is as follows:

- Establish `y + -y = e`
- Establish `x * (y + -y) = x * e` by multipliying both sides by `x`
- Simplify to `x * y + x * -y = e`
- Add `-(x*y)` to both sides and simplify

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
  l_distrib {x y z} := by cases x <;> cases y <;> cases z <;> aesop
  r_distrib {x y z} := by cases x <;> cases y <;> cases z <;> aesop
}

/-
Exercise
===

<ex /> Show

-/

example (x y : Spin) : x*y + x = x*(y+dn) := sorry


/-
Ring-Valued Sequences : Group
===

As an illustration for how you might use our `Ring` to define
a more complex mathematical object, consider the set of functions
```
ℕ → R
```
of sequences of elements from `R`.

To show sequences over `R` form a ring, we start by
showing sequence addition forms a `Group`.

-/

instance Seq.inst_group {R : Type u} [Ring R] : Group (ℕ → R) := {
  op f g n      := f n + g n,
  e n           := e,
  inv f n       := - f n,
  assoc {f g h} := by funext n; exact assoc,
  id_left {f}   := by funext n; exact id_left,
  inv_left {f}  := by funext n; exact inv_left
}

/-
Ring-Valued Sequences : Monoid
===

Show sequences form a `Monoid` is equally straightforward.
-/

instance Seq.inst_monoid {R : Type u} [Ring R] : Monoid (ℕ → R) := {
  mul f g n := (f n) * (g n),
  one n := one,
  mul_assoc {f g h} := by funext n; exact mul_assoc,
  mul_id_left {f}   := by funext n; rw[mul_id_left]
  mul_id_right {f}  := by funext n; rw[mul_id_right]
}

/-
Exercise
===

<ex /> Complete the above development showing `ℕ → R` forms a `Ring`.

<ex /> Show that if `R` is a `CommRing` then so is `ℕ → R`. Try using
`inferInstance` to reuse the code we're already written.

-/

/-
Exercise
===

<ex /> (Optional) Define an `Ideal` in `R` be the type:

-/

structure Ideal (R : Type u) [CommRing R] where
  I : R → Prop
  has_zero : I e
  closed {x y : R} : I x → I y → I (-x + y)
  absorb {r x : R} : I x → I (r * x) ∧ I (x * r)

/- Complete the following definition of the *principal ideal*
of an element `x : R` to be -/

def PrincipalIdeal {R : Type u} [CommRing R] (x : R) : Ideal R := {
  I y := ∃ r : R, y = x * r,
  has_zero := sorry,
  closed := sorry,
  absorb := sorry
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

class Field (F : Type u) extends CommRing F, Nontrivial F where
  minv : F → F
  minv_zero : minv e = e
  mul_inv_prop {x : F} : x ≠ e → mul x (minv x) = one

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
Example Field Identity
===

We only required `one * x = x` in our definition because we can prove the symmetric case:

-/

theorem mul_id_right : x * one = x := by
  rw[mulcomm]
  rw[mul_id_left]


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

/-
Spin is a a Nonempty Commutative Ring
===
-/

instance Spin.inst_nt : Nontrivial Spin := {
  exists_pair_ne := by
    use up, dn
    simp
}

instance Spin.inst_comm_ring : CommRing Spin := {
  mulcomm {x y} := by cases x <;> cases y <;> aesop
}

/-
Spin is a Field
===
-/

instance Spin.inst_field : Field Spin := {
  minv x := x
  minv_zero := by simp,
  mul_inv_prop {x} h := by cases x <;> simp_all[e]; rfl
}

/- Field theorems apply: -/

example : dn ≠ up := one_ne_e

/-
Mathlib's Algebra
===

The integers `ℤ` with `+` and `*` are the standard example of a commutative ring.
-/

#synth AddGroup ℤ              -- Int.instAddGroup
#synth CommMonoid ℤ            -- etc.
#synth _root_.CommRing ℤ

/-
The rationals `ℚ` with `+`, `*` and `x⁻¹` are the standard example of a field.
-/

#synth AddGroup ℚ               -- Rat.addGroup
#synth CommMonoid ℚ
#synth _root_.Field ℚ

/- And there are tactics -/

example (x y : ℤ) : x + y = y + x := by group
example (x y : ℤ) : 2*(x + y) = 2*y + 2*x := by ring
example (x y : ℚ) : 2*(x⁻¹ + y) = 2*y + 2*x⁻¹ := by field

/-
Exercises
===

<ex /> Show

-/

theorem one_inv : (one:F)⁻¹ = one := sorry

/-

<ex /> Instantiate `(ℤ,+)` as a `Field` (using the definition in this file,
not Mathlib's). For the properties, find them [here](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Int/Lemmas.html)
or by just checking `by apply?`.

You can do this all at once with `instance : Field ℤ` or by building up
`Group`, `Monoind`, `Ring`, `CommRing` and `Field` sequentially.

<ex /> (Optional) Show that in a `Field`, `(a*b)⁻¹ = (a⁻¹)*(b⁻¹)`.
You should build up several simpler identities about `Ring` before tackling this one.

-/

--hide
end
end
end Temp
end LeanW26
--unhide
