--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.flexible false

namespace LeanW26

/-
Embedding First Order Logic
===
-/

/-
Embedding First Order Logic
===
In this slide deck we embed First Order Logic into Lean by defining:

- An **abstract syntax** tree (AST) for first order logic expressions built from variables, predicates, `⊥`, `→`, and `∀`, from which one defines `∧`, `∨`, `¬`, and `∃`.

- An inductive definition of **provability**, denoted `Γ ⊢ φ`, that encodes the proof rules `ax`, `⊥-elim`, `→-intro`, `→-elim`, `∀-intro`, `∀-elim`, and `em`.

- A definition of **entailment**, denoted `Γ ⊨ φ`

- Examples from graph theory and the natural numbers.

- A proof of **soundness**: `Γ ⊢ φ → Γ ⊨ φ`

- A *partial* proof of **completness**: `Γ ⊢ φ → Γ ⊨ φ`

Functions are not defined directly, but are simulated using predicates.

-/

/-
Details of the Embedding
===
▸ **Variables** are represented using **Debruijn indices**. For example:

&nbsp;&nbsp;&nbsp; `all (ex (rel P ![1,0]))`   &nbsp;&nbsp;&nbsp;
represents                  &nbsp;&nbsp;&nbsp;
`∀ x . ∃ y . P(x,y)`

A comprehesive library of dozens of `@[simps]` supports substitution, lifting,
and renaming of variable indices crucial for the proof of soundness.

▸ **Signatures** contain predicate declarations with specific arities.
For example, a Graph theory signature with equality is denoted:
```lean
inductive Graph : Signature | E : Graph 2 | eq: Graph 2
```

▸ **Models** are represented as structures with interpretations as in:
```lean
def Cycle (n : ℕ): Model Graph (Fin n) := ⟨
  fun sym f => match sym with
    | E => f 0 = ((f 1) + 1) % n
    | eq => f 0 = f 1
⟩
```
-/

/-
Related Work
===

▸ A great book for First Order Logic is by Ederton: *A Mathematical
Introduction to Logic*.

▸ [Debruijn](https://en.wikipedia.org/wiki/De_Bruijn_index) was developed
in terms of the lambda calculus. It is explained in Arthur Charguéraud's *The Locally Nameless Representation*, JAR 2012 [Link](https://www.chargueraud.org/research/2009/ln/main.pdf) among other places.

▸ First order logic is already defined in Mathlib based on the
[Flypitch project](https://flypitch.github.io/), which is a formalization
of the proof of the independence of the continuum hypothesis.


-/


/-
Outline
===

The overall structure of the code to build this embedding is as follows.

- Variables
- Tuples
- Signatures
- Formulas
- Contexts and Provability
- Satisfiability and Entailment
- Soundness
- Completness (partial)

The code presented in this slide deck is contained in the source code
for the slide deck on [github](https://github.com/klavins/LeanW26).

However, as a standalone project, the code would be split up into
multiple files.

-/




/-
Variables
===
In first order logic we assume a countably infinite supply of variables `x₀`, `x₁`, `x₂`, ...,
which we identify with the natural numbers:
-/

abbrev Var := ℕ

/- We define a **substitution** of one variable for another as follows: -/

def Var.subst (s x : Var) (v : Var) : Var :=
  if v = x then s else v

notation:max t "[" x " ↦ " s "]" => Var.subst s x t

/- For example, -/

namespace Examples
  example : 1[2↦1] = 1 := rfl
  example : 1[1↦2] = 2 := rfl
end Examples

/-
Tuples
===
-/

abbrev Arity := ℕ

abbrev Tuple (k : Arity) := Fin k → Var

/- Tuples are easily expressed using Lean's `![...]` notation. For example, -/

--hide
namespace Examples
--unhide

def my_tuple : Tuple 3 := ![1,2,3]

--hide
end Examples
--unhide

/-
Formulas
===
The formulas of First Order Logic are defined in terms of a minimal set of connectives
and quantifiers, to keep proofs short.
-/

abbrev Signature := Arity → Type

inductive Formula (S : Signature)
  | bot     : (Formula S)
  | rel {k} : S k → Tuple k  → (Formula S)
  | imp     : (Formula S) → (Formula S) → (Formula S)
  | all     : (Formula S) → (Formula S)



/-
Derived Formulas
===
Other connectives and quantifiers are derived from the core syntax.
-/

--hide
section
namespace Formula
--unhide
variable {S : Signature}

def not (a : Formula S) := (imp a bot)
def or (a b : Formula S) := (imp (not a) b)
def and (a b : Formula S) := not (or (not a) (not b))
def top : Formula S := (not bot)
def ex (a : Formula S) := not (all (not a))
--hide
end Formula
end
--unhide

/-
Example: Graphs
===
A signature `(E)` for directed graphs may be defined as follows
-/

namespace Examples

inductive Graph : Signature
  | E   : Graph 2
  deriving Repr

open Formula Graph

/- in which we can express the simple graph properties: -/

def Graph.no_self_loops : Formula Graph :=
  all (not (rel E ![0,0]))

def Graph.completely_connected : Formula Graph :=
  all (all (rel E ![0,1]))


/-
Example: Natural Numbers
===
A signature `(0,succ,+,*,≤)` for the natural numbers may be defined
-/

inductive Nats : Signature
  | is_zero   : Nats 1
  | is_succ   : Nats 2
  | is_sum    : Nats 3
  | is_prod   : Nats 3
  | le        : Nats 2
  deriving Repr

open Nats

/- in which we can represent various properties of the natural numbers: -/

def Nats.one_plus_one := (Formula.and (rel is_zero ![0])
                         (Formula.and (rel is_succ ![0,1])
                         (Formula.and (rel is_succ ![1,2])
                         (rel is_sum ![1,1,2]))))
--hide
end Examples
--unhide

/-
Exercises
===

<ex /> Define a formula over graphs stating that a graph has an isolated vertex.

<ex /> Define a formula over natural numnbers stating that a number is prime.

<ex /> Define a signature for Group Theory and define a formula stating that a group is Abelian.

-/

/-
Shifting and Instantiating
===
To support Debruijn indexing, variables need to be shifted up and down when
adding and removing quantifiers. We define the notion of a `level` to
define how far we are shifting.
-/

abbrev Level := ℕ

def Var.shift (level : Level) (v : Var) : Var :=
  if v < level then v else v + 1

def Var.unshift (level : Level) (v : Var) : Var :=
  if v < level then v else v - 1


/-
Instantiation
===

When a formula of the form `all φ` is instantiated at a particular term `t`
we replace occurances of `x₀` with `t`.

This is supported at the variable
level by the following:

-/

def Var.inst_at (t : Var) (level : Level) (v : Var) : Var :=
  if v < level then v
  else if v = level then t
  else v - 1

/-
Variable Substitution Properties
===
We define simplifiying theorems for variable substitution.
-/

--hide
section
namespace Var
variable {level : Level} {t v s s' x y : Var}
--unhide

@[simp] theorem subst_eq : x[x↦s] = s := by simp[subst]

theorem subst_ne (h : t ≠ x) : t[x↦s] = t := by simp[subst, h]

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : v[x↦s][y↦t] = v[y↦t][x↦s[y↦t]] := by
  simp[subst]
  aesop

@[simp] theorem subst_succ_ne_succ (h : t ≠ x)
  : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by
  simp[subst, h]

@[simp] theorem subst_succ : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by
  by_cases h : t = x <;> simp [h]

/-
Variable Shifting and Instantiation Properties
===
To avoid having to do arithmetic and if-then-else reasoning in high level proofs, we prove a set of simplifiers for shifting and instantiating.
-/

@[simp] theorem unshift_shift : unshift level ∘ shift level = id := by
  --brief
  funext v
  simp[shift,unshift]
  split_ifs with h1 h2
  · rfl
  · have h3 : level < level := by
      have h4 : v < v + 1 := lt_add_one v
      have h5 : v < level := Nat.lt_trans h4 h2
      exact False.elim (h1 h5)
    exact False.elim ((lt_self_iff_false level).mp h3)
  · exact add_tsub_cancel_right _ _
  --unbrief

@[simp] theorem inst_at_lt (h : v < level) : inst_at t level v = v := by
  --brief
  simp [inst_at, h]
  --unbrief

@[simp] theorem inst_at_eq : inst_at t level level = t := by
  --brief
  simp [inst_at]
  --unbrief

@[simp] theorem inst_at_gt (h : level < v) : inst_at t level v = v - 1 := by
  --brief
  simp [inst_at, not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
  --unbrief

@[simp] theorem subst_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x ↦ s] = v := by
    --brief
   exact subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hx))
  --unbrief

@[simp] theorem subst_succ_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x+1 ↦ s+1] = v := by
  --brief
  exact subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv (Nat.le_succ_of_le hx)))
  --unbrief

/-
More simps
===
-/

@[simp] theorem inst_at_succ_of_le (hs : level ≤ s) : inst_at t level (s + 1) = s := by
  --brief
  simp [inst_at_gt (Nat.lt_succ_of_le hs)]
  --unbrief

@[simp] theorem inst_at_shift : inst_at t level (Var.shift level v) = v := by
  --brief
  by_cases h : v < level
  · simp [Var.shift, h]
  · simp [Var.shift, h, inst_at_succ_of_le (Nat.le_of_not_lt h)]
  --unbrief

@[simp] theorem subst_pred_of_gt_of_ne (hgt : level < v) (hne : v ≠ x + 1)
  : (v - 1)[x ↦ s] = v - 1 := by
  --brief
  apply subst_ne
  intro heq
  exact hne (Nat.eq_add_of_sub_eq (Nat.lt_of_le_of_lt (Nat.zero_le level) hgt) heq)
  --unbrief

theorem subst_inst_at (hs : level ≤ s) (hx : level ≤ x) :
    (inst_at t level v)[x ↦ s] =
    inst_at (t[x↦s]) level (v[x+1 ↦ s+1]) := by
  --brief
  by_cases h1 : v < level
  · simp [subst_of_lt_of_le h1 hx, subst_succ_of_lt_of_le h1 hx, inst_at_lt h1]
  by_cases h2 : v = level
  · simp [*,subst_ne (Nat.ne_of_lt (hx.trans_lt (Nat.lt_succ_self x))), inst_at_eq]
  · have h3 : v ≥ level := Nat.le_of_not_lt h1
    have hgt : level < v := Nat.lt_of_le_of_ne h3 (Ne.symm h2)
    rw [inst_at_gt hgt]
    by_cases h4 : v = x + 1
    · subst h4
      simp [subst_eq, inst_at_succ_of_le hs]
    · rw [subst_pred_of_gt_of_ne hgt h4, subst_ne h4, inst_at_gt hgt]
  --unbrief

--hide
end Var
end
--unhide

/-
Extending to Tuples
===

By composing variable operators with tuples, we can lift the standard
operations to tuples. Subsitution is simply:
-/

def Tuple.subst {k} (s x : Var) (tuple : Tuple k) : Tuple k :=
  (Var.subst s x) ∘ tuple

notation:max t "[" x " ↦ " s "]" => Tuple.subst s x t

/- And the other operations are -/

def Tuple.shift {k} (level : Level) (tuple : Tuple k): Tuple k :=
  (Var.shift level) ∘ tuple

def Tuple.unshift {k} (level : Level) (tuple : Tuple k): Tuple k :=
  (Var.unshift level) ∘ tuple

def Tuple.inst_at {k} (level : Level) (t : Var) (tuple : Tuple k) : Tuple k :=
  (Var.inst_at t level) ∘ tuple



/-
Theorems About Tuples
===
We similarly have a number of `@[simps]` for `Tuple`.
-/

--hide
section
namespace Tuple
variable {k : Arity} {level : Level} {s t x y : Var} {τ : Tuple k} {i : Fin k}
--unhide

@[simp] theorem unshift_shift
  : (unshift (k := k) level) ∘ (shift (k := k) level) = id := by
  --brief
  funext tuple
  simp[unshift,shift,←Function.comp_assoc]
  --unbrief

@[simp] theorem subst_apply
  : τ[x↦s] i = ((τ i)[x↦s]:Var) := rfl

@[simp] theorem inst_at_apply
  : inst_at level t τ i = Var.inst_at t level (τ i) := rfl

@[simp] theorem inst_at_shift
  : inst_at level t (shift level τ) = τ := by
  --brief
  funext i
  simp [shift, Var.inst_at_shift]
  --unbrief

@[simp] theorem inst_at_subst (hs : level ≤ s) (hx : level ≤ x) :
  (inst_at level t τ)[x↦s] = (τ[x+1↦s+1]).inst_at level (t[x↦s]) := by
  --brief
  funext i
  simp only [Tuple.subst, Tuple.inst_at, Function.comp]
  exact Var.subst_inst_at hs hx
  --unbrief

/-
More Theorems about Tuples
===
And last but not least:
-/

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : τ[x↦s][y↦t] = τ[y↦t][x↦s[y↦t]] := by
  --brief
  simp[subst,h₁,h₂,funext_iff]
  --unbrief

@[simp] theorem subst_id : τ[x↦x] = τ := by
  --brief
  simp[subst,funext_iff,Var.subst]
  intro _ hi
  exact Eq.symm hi
  --unbrief

/- While the `Var` simples are tedious and tricky, the `Tuple` proofs are easy extensions. -/

--hide
end Tuple
end
--unhide

/-
Exercises
===

<ex /> Show that substituting `x` for `y` and then `y` for `x` in a tuple does not necessarily result in the same tuple.

-/

/-
Substitution on Formulas
===
Substitution on formulas is defined inductively.
-/

def Formula.subst {S : Signature} (t : Var) (x : Var) : Formula S → Formula S
  | bot => bot
  | rel r tuple => rel r (Tuple.subst t x tuple)
  | imp φ ψ => imp (subst t x φ) (subst t x ψ)
  | all φ => all (subst (t+1) (x+1) φ)

notation:max φ "[" x " ↦ " s "]" => Formula.subst s x φ

/- For example: -/

--hide
namespace Examples
--unhide

def Nats.one_plus_one_alt := Nats.one_plus_one[2↦3]

/- results in a formula where the variable `x₃` represents `2` instead
of `x₂` representing `2`.-/

--hide
end Examples
--unhide

/-
Subtitution simps
===
The following substutition `@[simps]` make subsequent proofs much easier.
-/

--hide
section
namespace Formula
variable {S : Signature} {φ ψ : Formula S} {s x: Var} {k : Arity} {τ : Tuple k} {r : S k} {r₁ : S 1}
--unhide

@[simp] theorem subst_bot : (bot : Formula S)[x↦s] = bot := rfl
@[simp] theorem subst_imp : (imp φ ψ)[x↦s] = imp (φ[x↦s]) (ψ[x↦s]) := rfl
@[simp] theorem subst_not : not φ[x↦s] = (not φ)[x↦s] := rfl
@[simp] theorem subst_and : (and φ ψ)[x↦s] = and φ[x↦s] ψ[x↦s] := rfl
@[simp] theorem subst_all : (all φ)[x↦s] = all (φ[x+1↦s+1]) := rfl
@[simp] theorem subst_rel : (rel r τ)[x↦s] = rel r (τ[x↦s]) := rfl
@[simp] theorem subst_rel0 : (rel r₁ ![0])[0↦s] = rel r₁ ![s] := by
  --brief
  simp[funext_iff]
  --unbrief
@[simp] theorem subst_rel0' : (rel r₁) ![0][0↦s]  = rel r₁ ![s] := by
  --brief
  simp[funext_iff]
  --unbrief

--hide
end Formula
end
--unhide

/-
Renamers
===

Next we define an infrastructure that can be used to rename all free variables in a formula.

-/

abbrev Renamer := Var → Var

def Renamer.lift (f : Renamer) : Renamer
  | 0 => 0
  | n+1 => (f n) + 1
--hide
section
variable {f g : Renamer} {level : Level}
--unhide
@[simp] theorem Renamer.lift_id : lift id = id := by
  --brief
  funext i
  simp[lift]
  cases i <;> rfl
  --unbrief

@[simp] theorem Renamer.lift_comp : lift (g ∘ f) = lift g ∘ lift f := by
  --brief
  funext i
  simp[lift]
  cases i <;> rfl
  --unbrief

@[simp] theorem Renamer.lift_shift
  : lift f ∘ Var.shift 0 = Var.shift 0 ∘ f := by
  --brief
  funext i
  simp[lift]
  rfl
  --unbrief

@[simp] theorem hlift : Renamer.lift (Var.shift level)
                        = Var.shift (level + 1) := by
  --brief
    funext v
    cases v
    · simp [Renamer.lift, Var.shift]
    · simp only [Renamer.lift, Var.shift, Nat.succ_lt_succ_iff]
      split_ifs <;> rfl
  --unbrief

--hide
end
--unhide

/-
Rename
===
We now define renaming for formulas
-/

def Formula.rename {S : Signature} (φ : Formula S) (f : Renamer) : Formula S :=
  match φ with
    | bot => bot
    | rel r t => rel r (f ∘ t)
    | imp ψ₁ ψ₂ => imp (rename ψ₁ f) (rename ψ₂ f)
    | all ψ => all (rename ψ (f.lift))

/- And associated @simps -/

--hide
section
open Formula
variable {S : Signature} {φ : Formula S} {f g : Renamer} {t : Var} {level : Level}
--unhide

@[simp] theorem rename_id : φ.rename id = φ := by
  --brief
  induction φ with
  | bot => rfl
  | rel r t => simp [rename]
  | imp ψ₁ ψ₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]
  | all ψ ih => simp [rename, ih]
  --unbrief

@[simp] theorem rename_comp
  : (φ.rename f).rename g = φ.rename (g ∘ f) := by
  --brief
  induction φ generalizing f g with
  | bot => rfl
  | rel r t => simp [rename, Function.comp_assoc]
  | imp ψ₁ ψ₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]
  | all ψ ih => simp [rename, ih]
  --unbrief

@[simp] theorem lift_inst_at  :
    Renamer.lift (Var.inst_at t level) =
    Var.inst_at (t+1) (level+1) := by
  --brief
  funext v
  cases v with
  | zero => simp [Renamer.lift, Var.inst_at]
  | succ n =>
     simp[Renamer.lift, Var.inst_at]
     split_ifs
     · simp
     · simp
     · apply Nat.succ_pred_eq_of_ne_zero
       aesop
  --unbrief

--hide
end
--unhide



/-
Instantiation for Formulas
===
Applying a formula of the form `all φ` to a particular term `t` is called instantiating `φ` with `t`.

We define a general notion of instantition at any level.
-/

open Formula in
def Formula.inst_at {S : Signature} (t : Var) (level : Level)
  : Formula S → Formula S
  | bot         => bot
  | rel r tuple => rel r (tuple.inst_at level t)
  | imp φ ψ     => imp (inst_at t level φ) (inst_at t level ψ)
  | all φ       => all (inst_at (t+1) (level+1) φ)

/- And then we define instantiation at `0`. -/

def Formula.inst {S : Signature} (t : Var) : Formula S → Formula S :=
  inst_at t 0

/-
Instantiation Example
===

For example, instantiating `∀ x . E(x,y)` with `z` gives `∀ x . E(x,z)`.

The the example below, we use `10` for `z`.

-/
--hide
namespace Examples
--unhide

open Graph Formula

example : (all (rel E ![0,1])).inst 10
        = (all (rel E ![0,11])) := by
  simp[inst,inst_at,Tuple.inst_at,funext_iff,Var.inst_at]

--hide
end Examples
--unhide

/-
Instantiation simps
===
We prove a number of results about instantiation.
-/

--hide
section
namespace Formula
variable {S : Signature} {φ ψ : Formula S} {s x y t : Var} {L : Level}
--unhide
@[simp] theorem inst_eq : φ.inst t = φ.inst_at t 0 := rfl
@[simp] theorem inst_at_bot : (bot : Formula S).inst_at t L = bot := rfl
@[simp] theorem inst_at_imp
  : (imp φ ψ).inst_at t L = imp (φ.inst_at t L) (ψ.inst_at t L) := rfl
@[simp] theorem inst_at_all
  : (all φ).inst_at t L = all (φ.inst_at (t+1) (L+1)) := rfl
@[simp] theorem inst_at_rel {k : Arity} {r : S k} {τ : Tuple k}
  : (rel r τ).inst_at t L = rel r (τ.inst_at L t) := rfl
@[simp] theorem subst_id : φ[x↦x] = φ := by
  --brief
  induction φ generalizing x <;> simp[*]
  --unbrief

theorem inst_at_subst (h₁ : L ≤ x) (h₂ : L ≤ s)
  : (φ.inst_at t L)[x↦s] = φ[x+1↦s+1].inst_at t[x↦s] L := by
  --brief
  induction φ generalizing t s L x with
  | bot => rfl
  | rel t τ => simp[*]
  | imp f g ihf ihg => simp[*]
  | all f ih =>
      simp [ih (Nat.succ_le_succ h₁) (Nat.succ_le_succ h₂)]
  --unbrief

theorem inst_subst {S : Signature} (φ : Formula S) (s x t : Var)
  : (φ.inst t)[x↦s] = φ[x+1↦s+1].inst t[x↦s]  := by
  --brief
  exact inst_at_subst (Nat.zero_le x) (Nat.zero_le s)
  --unbrief


/-
Example Proof
===
Most of these proofs are simple. Here's a slightly complicated one:
-/
@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : φ[x↦s][y↦t] = φ[y↦t][x↦s[y↦t]] := by
  induction φ generalizing t s x y with
  | bot => rfl
  | rel r τ => simp[subst, *]
  | imp f g ihf ihg => simp[subst, *]
  | all f ih =>
    have := @ih (s+1) (x+1) (y+1) (t+1)
                ((add_ne_add_left 1).mpr h₁)
                ((add_ne_add_left 1).mpr h₂)
    simp[this]

/-
Exercises
===

<ex /> Show that `subst_subst` is not necessariy true when if we drop the requirement that `x ≠ y`.

-/

/-
Shifting
===

We now start building the definition of provability, starting with shifting.

Shifting is renaming by shifting at `0`. It is used in the definition of `∀-Intro`:
-/

def shift {S : Signature} (φ : Formula S) := φ.rename (Var.shift 0)

/- The interaction between instantiation and shift is a key property. -/

@[simp] theorem inst_shift : (φ.shift).inst x = φ := by
  --brief
  suffices h : ∀ (level : Level), (φ.rename (Var.shift level)).inst_at x level = φ from h 0
  induction φ generalizing x with
  | bot => intros; rfl
  | rel r τ =>
    intros
    simp [rename]
    exact Tuple.inst_at_shift
  | imp f g ihf ihg => simp [rename, ihf, ihg]
  | all f ih => simp [rename, ih]
  --unbrief

theorem inst_at_eq_rename
  : φ.inst_at t L = φ.rename (Var.inst_at t L) := by
  --brief
  induction φ generalizing t L with
  | bot => rfl
  | rel r τ => simp[Formula.inst_at, Formula.rename, Tuple.inst_at]
  | imp g h ihg ihh => simp[Formula.inst_at, Formula.rename, ihg, ihh]
  | all g ih =>
    simp only [Formula.inst_at, Formula.rename]
    simp[lift_inst_at]
    exact ih
  --unbrief

/- Both of these proofs require proof by induction un the structure of the formula. -/

--hide
end Formula
end
--unhide


/-
Provability
===
-/

abbrev Context S := Set (Formula S)

open Formula in
inductive Provable {S : Signature} : Context S → Formula S → Prop
  | ax {Γ φ}              : (h : φ ∈ Γ) → Provable Γ φ
  | bot_elim {Γ φ}        : Provable Γ bot → Provable Γ φ
  | im_intro {Γ φ ψ}      : Provable (Γ ∪ {φ}) ψ → Provable Γ (imp φ ψ)
  | im_elim {Γ φ ψ}       : Provable Γ (imp φ ψ) → Provable Γ φ → Provable Γ ψ
  | all_intro {Γ φ}       : Provable (shift '' Γ) φ → Provable Γ (all φ)
  | all_elim {Γ φ t}      : Provable Γ (all φ) → Provable Γ (inst t φ)
  | em {Γ φ}              : Provable Γ (or (not φ) φ)

infix:50 " ⊢ " => Provable

/-
Provability Example
===
To illustrate the how proofs work in this system, we do a few proofs.
-/

--hide
namespace Examples
open Formula Provable
--unhide

/- Now we can do proofs like this one showing `(∀ x, P x) → (∀ x. Px)`. -/

example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (all (rel P ![0])) := by
  apply im_intro
  apply ax
  simp

/-
Another Example
===
Here we show
```
∅ ⊢ ∀x, P(x) → P(5)
```
to test `all_elim` -/

example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (rel P ![5]) := by
  apply im_intro
  have : rel P ![5] = (rel P ![0]).inst 5 := by
    simp[Tuple.inst_at,funext_iff]
  rw[this]
  apply all_elim
  apply ax
  simp

--hide
end Examples
--unhide

/-
Exercises
===

<ex /> Show the following:

-/

section
namespace Examples

  open Formula Provable

  example {S : Signature} {P Q : S 1}
    : {all (all (rel P ![0]))} ⊢ rel P ![3] := by
    sorry

end Examples
end

/-
Models
===
While the AST and provability define a syntax, a
**model** defines a universe over which variables live, and a
**semantics** for each predicate in a signature.
-/

universe u

structure Model (S : Signature) (α : Type u) where
  interp {arity} : S arity → (Fin arity → α) → Prop

/- For example, here is a model of a simple signature. -/
--hide
namespace Examples
--unhide
inductive Plain : Signature | P : Plain 1 | Q : Plain 1

open Plain in
def MP : Model Plain ℕ := {
  interp := fun sym f => match sym with
    | P => Even (f 0)
    | Q => Odd (f 0)
}
--hide
end Examples
--unhide

/-
Assignments
===
An **assignment** is a function from variables to values of some type `α`.
-/

def Assignment (α : Type u) := Var → α

/- We operate on assignments with the following. -/

def update {α : Type u} (A : Assignment α) (v : α) : Assignment α :=
  fun j => if j = 0 then v else A (j-1)

def update_at {α : Type u} (x : Var) (v : α) (A : Assignment α) : Assignment α :=
  fun j => if j = x then v else A j

def inst_assign {α : Type u} (A : Assignment α) (t : Var) (L : Level)
  : Assignment α := fun j => if      j < L then A j
                             else if j = L then A t
                             else               A (j - 1)


/-
Satisfaction
===
A model `M` and an assignment `A` **satisfies** a formula if the formula
holds when interpreted under `M` with assignment `A`. Formally,
-/

open Formula in
def satisfies {S : Signature} {α : Type u}
  (M : Model S α) (A : Assignment α) (f : Formula S) : Prop :=
  match f with
    | bot => false
    | rel r t => M.interp r (A ∘ t)
    | imp g h => satisfies M A g → satisfies M A h
    | all g  => ∀ x : α, satisfies M (update A x) g

/- We define *models* as satisfaction under any assignment. -/

def models {S : Signature} {α : Type u} (M : Model S α) (f : Formula S) :=
  ∀ a, satisfies M a f

/-
Example
===
Define a cyclic graph:
-/

--hide
namespace Examples
open Graph
--unhide

def Cycle (n : ℕ) : Model Graph (Fin n) := ⟨
  fun sym tuple => match sym with
  | E => tuple 0 = ((tuple 1) + 1) % n ⟩

/- The a cycle with one node has one (and only one) self loop -/
example : ¬models (Cycle 1) Graph.no_self_loops := by
  intro h
  have := h (fun _ => 0)
  simp[no_self_loops,Formula.not,satisfies,Cycle] at this

/- While a cycle with two nodes does not: -/
example : models (Cycle 2) Graph.no_self_loops := by
  intro A v h
  fin_cases v <;> simp_all[satisfies,Cycle,update]

--hide
end Examples
--unhide

/-
Exercise
===

<ex /> Define a Model for the signature `Nats` with the usual definition of
`zero`, `succ`, `add`, `prod`, and `le`.

<ex /> Show the model satisfies `Nats.one_plus_one`.

-/

/-
Entailment
===
A context `Γ` entails a formula `φ` if for all models `M` and assignments `A`, if
`M` and `A` satisfy every formula in `Γ`, then `M` and `A` satisfy `φ`.
-/

def entails {S : Signature} (Γ : Context S) (φ : Formula S) : Prop :=
 ∀ {β : Type} (M : Model S β) (A : Assignment β),
 (∀ ψ ∈ Γ, satisfies M A ψ) → satisfies M A φ

infix:25 " ⊨ " => entails

/- For example, -/

--hide
namespace Examples
open Graph Formula
--unhide

example {S : Signature} {P : S 1}
  : ∅ ⊨ imp (rel P ![0]) (rel P ![0]) := by
  intro β M A h1 h2
  exact h2

--hide
end Examples
--unhide

/-
<div class='fn'>
In the definition of entails, <tt>β : Type</tt> instead of <tt>β : Type v</tt>.
Unfortunately, Lean doesn't support universe quantification inside <tt>Prop</tt>.
I can't figure out a way around this.
</div>

-/


/-
Theorems about Satisfies
===
We prove the follow help theorems about satisfaction and how it interacts with
lifting, renaming and instantiation.
-/

--hide
variable {α : Type u} {S : Signature} {Γ : Context S} {M : Model S α}
         {φ ψ : Formula S} {a : Assignment α} {x : α} {f : Renamer}
         {t : Var} {level : Level}
--unhide

theorem update_comp_lift : update a x ∘ f.lift = update (a ∘ f) x := by
  --brief
  funext j; cases j with
  | zero => simp [update, Renamer.lift]
  | succ n => simp [Function.comp, update, Renamer.lift]
  --unbrief

theorem satisfies_rename : satisfies M a (φ.rename f) ↔
                           satisfies M (a ∘ f) φ := by
  --brief
  induction φ generalizing a f with
  | bot => simp [satisfies, Formula.rename]
  | rel r t => simp [satisfies, Function.comp_assoc, Formula.rename]
  | imp g h ihg ihh => simp [satisfies, ihg, ihh, Formula.rename]
  | all g ih =>
    simp only [satisfies, Formula.rename]
    constructor
    · intro h x
      have := (@ih (update a x) f.lift).mp (h x);
      rwa [update_comp_lift] at this
    · intro h x
      apply (@ih (update a x) f.lift).mpr
      rw [update_comp_lift]
      exact h x
  --unbrief

theorem inst_assign_comp : a ∘ Var.inst_at t level =
                           inst_assign a t level := by
  --brief
  funext j; simp only [Function.comp, Var.inst_at, inst_assign]; split_ifs <;> rfl
  --unbrief

theorem satisfies_inst_at : satisfies M a (φ.inst_at t level) ↔
                            satisfies M (inst_assign a t level) φ := by
  --brief
  rw [Formula.inst_at_eq_rename, satisfies_rename, inst_assign_comp]
  --unbrief

/-
Soundness
===
Soundness means that everything provable is also true: `Γ ⊢ φ → Γ ⊨ φ`.

We prove soundness for each possible way the proof `Γ ⊢ φ` might end.
-/

theorem sound_ax (h : φ ∈ Γ) : Γ ⊨ φ := by
  intro α M a hψ
  exact hψ φ h

theorem sound_bot_elim (h : Γ ⊨ Formula.bot) : Γ ⊨ φ := by
  intro α M a hΓ
  exact absurd (h M a hΓ) (by simp [satisfies])

theorem sound_im_intro (h : Γ ∪ {φ} ⊨ ψ) : Γ ⊨ Formula.imp φ ψ := by
  intro α M a hΓ hφ
  exact h M a (fun ω hω => by
    cases hω with
    | inl h1 => exact hΓ ω h1
    | inr h1 => simp at h1; rw [h1]; exact hφ)

/-
Soundness Continued
===
-/

theorem sound_im_elim (h₁ : Γ ⊨ Formula.imp φ ψ) (h₂ : Γ ⊨ φ) : Γ ⊨ ψ := by
  intro α M a hΓ
  exact h₁ M a hΓ (h₂ M a hΓ)

theorem sound_all_intro (h : Formula.shift '' Γ ⊨ φ) : Γ ⊨ Formula.all φ := by
  intro α M a hΓ x
  exact h M (update a x) (fun χ hχ => by
    obtain ⟨ψ, hψ, rfl⟩ := hχ
    rw [show ψ.shift = ψ.rename (Var.shift 0) from rfl, satisfies_rename]
    exact hΓ ψ hψ)

/-
Soundess Continued
===
-/

theorem sound_all_elim (h : Γ ⊨ Formula.all φ) : Γ ⊨ φ.inst t := by
  intro α M a hψ
  rw [Formula.inst_eq, satisfies_inst_at]
  have : inst_assign a t 0 = update a (a t) :=
    funext fun j => by simp [inst_assign, update]
  rw [this]
  exact h M a hψ (a t)

theorem sound_em : Γ ⊨ Formula.or (Formula.not φ) φ:= by
  intro  α M a hψ h1
  unfold Formula.not at h1
  simp[satisfies] at h1
  exact h1

/-
Soundess Finished
===
And now the main result:
-/

open Provable Formula in
theorem sound : Γ ⊢ φ → Γ ⊨ φ := by
  intro h
  induction h with
  | ax h                 => exact sound_ax h
  | bot_elim _ ih        => exact sound_bot_elim ih
  | im_intro _ ih        => exact sound_im_intro ih
  | im_elim _ _ ih₁ ih₂  => exact sound_im_elim ih₁ ih₂
  | all_intro _ ih       => exact sound_all_intro ih
  | all_elim _ ih        => exact sound_all_elim ih
  | em                   => exact sound_em



/-
Completeness
===
Completness means `Γ ⊨ φ → Γ ⊢ φ`, which was proved by Gödel in 1929.

This theorem is more complex than soundness and at this point I have it only partially finished.

-/

/-
Incompleteness
===
Completeness is not to be confused with incompletness. Gödel showed the remarkable result that
> There exists `φ` such that `models ℕ φ` but `PA ⊬ φ` and `PA ⊬ ¬φ`

where `PA` is the set of *Peano Axioms*:
```lean
1. ∀x, S(x) ≠ 0
2. ∀x ∀y, S(x) = S(y) → x = y
3. ∀x, x + 0 = x
4. ∀x ∀y, x + S(y) = S(x + y)
5. ∀x, x × 0 = 0
6. ∀x ∀y, x × S(y) = (x × y) + x
7. (φ(0) ∧ ∀x, φ(x) → φ(S(x))) → ∀x, φ(x)
```

The GIT was proved by `Gödel` in 1931.
-/



/-
Future Work
===

Spring 2026: Weekly research meetings on formalizing logic.

-/


--hide
end LeanW26
--unhide
