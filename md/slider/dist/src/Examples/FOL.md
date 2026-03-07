
Embedding First Order Logic
===


Embedding First Order Logic
===
In this slide deck we embed First Order Logic into Lean by defining:

- An **abstract syntax** tree (AST) for first order logic expressions built from variables, predicates, `⊥`, `→`, and `∀`, from which one defines `∧`, `∨`, `¬`, and `∃`.

- An inductive definition of **provability**, denoted `Γ ⊢ φ`, that encodes the proof rules `ax`, `⊥-elim`, `→-intro`, `→-elim`, `∀-intro`, `∀-elim`, and `em`.

- A definition of **entailment**, denoted `Γ ⊨ φ`

- Examples from graph theory and the natural numbers.

- A proof of **soundness**: `Γ ⊢ φ → Γ ⊨ φ`

- A *partial* proof of **completness**: `Γ ⊨ φ → Γ ⊢ φ`

Functions are not defined directly, but are simulated using predicates.



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


Related Work
===

▸ A great book for First Order Logic is by Ederton: *A Mathematical
Introduction to Logic*.

▸ [Debruijn](https://en.wikipedia.org/wiki/De_Bruijn_index) was developed
in terms of the lambda calculus. It is explained in Arthur Charguéraud's *The Locally Nameless Representation*, JAR 2012 [Link](https://www.chargueraud.org/research/2009/ln/main.pdf) among other places.

▸ First order logic is already defined in Mathlib based on the
[Flypitch project](https://flypitch.github.io/), which is a formalization
of the proof of the independence of the continuum hypothesis. This project was
developed separately, for purposes of self-edification.

▸ For connections to category theory: *First Order Categorical Logic
Model-Theoretical Methods in the Theory of Topoi and Related Categories*, by
Michael Makkai and Gonzalo E. Reyes.




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

The code presented in this slide deck is contained in the source code
for the slide deck on [github](https://github.com/klavins/LeanW26).

However, as a standalone project, the code would be split up into
multiple files. An example of how this would look is at:

> [https://github.com/klavins/LeanFOL](https://github.com/klavins/LeanFOL)



Variables
===
In a first order logic formula like
```
Q(x₀) ∨ ∀ x₁, P(x₀,x₁) → ∃ x₂, Q(x₂)
```
we have variables `x₀`, `x₁`, and `x₂` and tuples of variables `(x₀)`, `(x₀,x₁)` and `(x₂)`.

- Variables are indexed by natural numbers.

- The formula has subformulas bound with different numbers of quantifiers, which we call the level of the subformula.

These are all natural numbers.

```lean
abbrev Var := ℕ
abbrev Level := ℕ
```

Tuples
===

Tuples have an Arity (number of elements) and an assignment of location to a variable. This cam be represented as:


```lean
abbrev Arity := ℕ
abbrev Tuple (k : Arity) := Fin k → Var
```

For example,

```lean
--hide
namespace Examples
--unhide

def my_tuple : Tuple 3 := ![1,3,0]

--hide
end Examples
--unhide
```
 Represents `(x₁,x₃,x₀)`

Signatures
===
A signature is a function from `Arity` into `Type`.

```lean
abbrev Signature := Arity → Type
```

For example, a signature for graphs is

```lean
inductive Graph : Signature
  | E   : Graph 2
```
 and for numbers might be 
```lean
inductive Nats : Signature
  | is_zero   : Nats 1
  | is_succ   : Nats 2
  | is_sum    : Nats 3
  | is_prod   : Nats 3
  | le        : Nats 2
  | eq        : Nats 2
```

The Abstract Syntax Tree
===
From these basic definitions we can define Formulas inductively.

```lean
inductive Formula (S : Signature)
  | bot     : (Formula S)
  | rel {k} : S k → Tuple k  → (Formula S)
  | imp     : (Formula S) → (Formula S) → (Formula S)
  | all     : (Formula S) → (Formula S)

open Formula
```

Derived Formulas
===
Other connectives and quantifiers are derived from the core syntax.

```lean
namespace Formula

def not {S : Signature} (a : Formula S) := (imp a bot)
def or {S : Signature} (a b : Formula S) := (imp (not a) b)
def and {S : Signature} (a b : Formula S) := not (or (not a) (not b))
def top {S : Signature} : Formula S := (not bot)
def ex {S : Signature} (a : Formula S) := not (all (not a))

end Formula
```

Examples
===

Two Formulas over `Graph` signature is: 
```lean
def Graph.no_self_loops : Formula Graph :=
  all (not (rel E ![0,0]))

def Graph.completely_connected : Formula Graph :=
  all (all (rel E ![0,1]))
```
 A formula over `Nats` is 
```lean
def Nats.one_plus_one := (Formula.and (rel is_zero ![0])
                         (Formula.and (rel is_succ ![0,1])
                         (Formula.and (rel is_succ ![1,2])
                         (rel is_sum ![1,1,2]))))
```

Renaming Variables
===

We define an infrastructure that can be used to rename all free variables in a formula.


```lean
abbrev Renamer := Var → Var

def Renamer.lift (f : Renamer) : Renamer
  | 0 => 0
  | n+1 => (f n) + 1

def Formula.rename {S : Signature}
                   (φ : Formula S) (f : Renamer) : Formula S :=
  match φ with
    | bot => bot
    | rel r t => rel r (f ∘ t)
    | imp ψ₁ ψ₂ => imp (rename ψ₁ f) (rename ψ₂ f)
    | all ψ => all (rename ψ (f.lift))
```

Example Renaming
===
For example, renaming `∀ x₀ . ¬E(x₀,x₁)` with `x ↦ x+1` gives `∀ x₀ . ¬E(x₀,x₂)`.
The bound variable remains untouched, while the free variable is renamed.

```lean
open Graph in
example : (all (not (rel E ![0,1]))).rename (fun _ => 100)
         = all (not (rel E ![0,101])) := by
  simp[rename,Formula.not,funext_iff]
  constructor
  · simp[Renamer.lift]
  · simp[Renamer.lift]
```

Shifting
===
Shifting is increments variables above a certain level.

```lean
def Var.shift (level : Level) (v : Var) : Var :=
  if v < level then v else v + 1
```
 We use it to define shifting for a formula, for which we only need level=0. 
```lean
def Formula.shift {S : Signature} (φ : Formula S) := φ.rename (Var.shift 0)
```
 For example: 
```lean
open Graph in
example : (all (not (rel E ![0,1]))).shift
         = all (not (rel E ![0,2])) := by
  simp[shift,rename,Formula.not,funext_iff]
  constructor
  · simp[Renamer.lift]
  · simp[Renamer.lift,Var.shift]
```

Instantiating
===

Applying a formula of the form `all φ` to a particular term `t`.



```lean
def Var.inst_at (t : Var) (level : Level) (v : Var) : Var :=
  if v < level then v
  else if v = level then t
  else v - 1

def Tuple.inst_at {k} (level : Level) (t : Var) (tuple : Tuple k) : Tuple k :=
  (Var.inst_at t level) ∘ tuple

def Formula.inst_at {S : Signature} (t : Var) (level : Level)
  : Formula S → Formula S
  | bot         => bot
  | rel r tuple => rel r (tuple.inst_at level t)
  | imp φ ψ     => imp (inst_at t level φ) (inst_at t level ψ)
  | all φ       => all (inst_at (t+1) (level+1) φ)

def Formula.inst {S : Signature} (t : Var) : Formula S → Formula S :=
  inst_at t 0
```

Instantation Example
===
For example, suppose we have the formula `∀ x. ∀ y . E(x,y)`. To apply this formula to `z`, we put `z` in for `x` in `∀ y . E(x,y)` to get `∀ y . E(z,y)`.

```lean
open Graph in
example : (all (rel E ![1,0])).inst 10
        = (all (rel E ![11,0])) := by
  simp[inst,inst_at,Tuple.inst_at,funext_iff,Var.inst_at]
```

Provability
===
We define a `Context` to be a set of formulas

```lean
abbrev Context S := Set (Formula S)
```
 Then we define `Γ ⊢ φ` to mean that from the formulas in `Γ` we can prove `φ`.
```lean
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
```

Provability Example
===
To illustrate the how proofs work in this system, we do a few proofs.

```lean
--hide
open  Provable
--unhide
```
 Now we can do proofs like this one showing `(∀ x, P x) → (∀ x. Px)`. 
```lean
example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (all (rel P ![0])) := by
  apply im_intro
  apply ax
  simp
```

Another Example
===
Here we show
```
∅ ⊢ ∀x, P(x) → P(5)
```
as a test the `all_elim` rule: 
```lean
example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (rel P ![5]) := by
  apply im_intro
  have : rel P ![5] = (rel P ![0]).inst 5 := by
    simp[Tuple.inst_at,funext_iff,inst,inst_at,Var.inst_at]
  rw[this]
  apply all_elim
  apply ax
  simp
```

Assignments
===
An assignment is a mapping from variables to values. For values, we use some type `α` that depends on the application.

```lean
universe u

def Assignment (α : Type u) := ℕ → α
```
 We define an update to an assignment `A` as inserting a value `v` in
for `A 0` and shifting all other variable assignments. 
```lean
def update {α : Type u} (A : Assignment α) (v : α) :=
  fun j => if j=0 then v else A (j-1)
```

Models
===
A model is an interpretation of a signature, assigning specific predicates to each predicate symbols.

```lean
structure Model (S : Signature) (α : Type u) where
  interp {arity} : S arity → (Fin arity → α) → Prop
```
 For example, a `Model` for `Graph` is a particular set of nodes and edges, such as a cycle graph:

```lean
open Graph in
def Cycle (n : ℕ) : Model Graph (Fin n) := ⟨
  fun sym tuple => match sym with
  | E => tuple 0 = ((tuple 1) + 1) % n ⟩
```

Satisfaction
===
A model `M` and an assignment `A` **satisfies** a formula if the formula
holds when interpreted under `M` with assignment `A`. Formally,

```lean
open Formula in
def satisfies {S : Signature} {α : Type u}
  (M : Model S α) (A : Assignment α) (f : Formula S) : Prop :=
  match f with
    | bot => false
    | rel r t => M.interp r (A ∘ t)
    | imp g h => satisfies M A g → satisfies M A h
    | all g  => ∀ x : α, satisfies M (update A x) g
```

Models
===

 We define *models* as satisfaction under any assignment. 
```lean
def models {S : Signature} {α : Type u} (M : Model S α) (f : Formula S) :=
  ∀ a, satisfies M a f
```
 The a cycle with one node has one (and only one) self loop 
```lean
open Graph in
example : ¬models (Cycle 1) Graph.no_self_loops := by
  intro h
  have := h (fun _ => 0)
  simp[no_self_loops,Formula.not,satisfies,Cycle] at this
```
 While a cycle with two nodes does not: 
```lean
example : models (Cycle 2) Graph.no_self_loops := by
  intro A v h
  fin_cases v <;> simp_all[satisfies,Cycle,update]
```

Entailment
===

A context `Γ` entails a formula `φ` if for all models `M` and assignments `A`, if
`M` and `A` satisfy every formula in `Γ`, then `M` and `A` satisfy `φ`.

```lean
abbrev entails {S : Signature}
               (Γ : Context S) (φ : Formula S) : Prop :=
 ∀ {β : Type} (M : Model S β) (a : Assignment β),
   (∀ ψ ∈ Γ, satisfies M a ψ) → satisfies M a φ

infix:25 " ⊨ " => entails
```
 For example, here we show `P(0) → P(0)` is a tautology. 
```lean
example {S : Signature} {P : S 1}
  : ∅ ⊨ imp (rel P ![0]) (rel P ![0]) := by
  intro β M A h1 h2
  exact h2
```

<div class='fn'>
In the definition of entails, <tt>β : Type</tt> instead of <tt>β : Type v</tt>.
Unfortunately, Lean doesn't support universe quantification inside <tt>Prop</tt>.
I can't figure out a way around this.
</div>



Soundness Plan
===
Our goal is now to prove that everything provable is also true:
```lean
Γ ⊢ φ → Γ ⊨ φ
```
To get there, we need a number of helper theorems and simps. 
```lean
--hide
namespace Formula

variable {S : Signature} {φ ψ : Formula S} {f g : Renamer}
         {s x y t : Var} {level : Level}
--unhide
```

Here's a super simple one, as an example, that is just a *definitional simp*.

```lean
@[simp] theorem inst_eq : φ.inst t = φ.inst_at t 0 := rfl
```

Lifting and Instantiation
===

```lean
@[simp] theorem lift_inst_at (t : Var) (level : Level):
    Renamer.lift (Var.inst_at t level) = Var.inst_at (t+1) (level+1) := by
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
```

Instantiaing and Renaming
===

```lean
theorem inst_at_eq_rename : φ.inst_at t level
                          = φ.rename (Var.inst_at t level) := by
  induction φ generalizing t level with
  | bot => rfl
  | rel r τ => simp[Formula.inst_at, Formula.rename, Tuple.inst_at]
  | imp g h ihg ihh => simp[Formula.inst_at, Formula.rename, ihg, ihh]
  | all g ih =>
    simp only [Formula.inst_at, Formula.rename]
    simp[lift_inst_at]
    exact ih


--hide
end Formula
--unhide
```

Relating Updating and Lifting
===

```lean
--hide
section

variable {α : Type u} {S : Signature} {Γ : Context S} {M : Model S α}
         {φ ψ : Formula S} {a : Assignment α} {x : α} {f : Renamer}
         {t : Var} {level : Level}
--unhide

theorem update_comp_lift : update a x ∘ f.lift = update (a ∘ f) x := by
  funext j; cases j with
  | zero => simp [update, Renamer.lift]
  | succ n => simp [Function.comp, update, Renamer.lift]
```

Relating Satisfies and Rename
===

```lean
lemma satisfies_rename : satisfies M a (φ.rename f)
                       ↔ satisfies M (a ∘ f) φ := by
  induction φ generalizing a f with
  | bot => simp [satisfies, Formula.rename]
  | rel r t => simp [satisfies, Function.comp_assoc, Formula.rename]
  | imp g h ihg ihh => simp [satisfies, ihg, ihh, Formula.rename]
  | all g ih =>
    simp only [satisfies, Formula.rename]
    constructor <;> intro h x
    · have := (@ih (update a x) f.lift).mp (h x)
      rwa [update_comp_lift] at this
    · apply (@ih (update a x) f.lift).mpr
      rw [update_comp_lift]
      exact h x
```

Assignments, instances and shifting
===

```lean
def inst_assign {α : Type u} (A : Assignment α) (t level : ℕ)
  : Assignment α :=
  fun j => if j < level then A j
          else if j = level then A t
          else A (j - 1)

theorem inst_assign_comp : a ∘ Var.inst_at t level
                         = inst_assign a t level := by
  funext j; simp only [Function.comp, Var.inst_at, inst_assign]
  split_ifs <;> rfl

theorem satisfies_inst_at
   : satisfies M a (φ.inst_at t level)
   ↔ satisfies M (inst_assign a t level) φ := by
  rw [Formula.inst_at_eq_rename, satisfies_rename, inst_assign_comp]

@[simp] theorem update_shift : update a x ∘ Var.shift 0 = a := by
  funext j
  simp [Function.comp, update, Var.shift]
```

Soundness
===
Now we prove soundness for each possible way the proof `Γ ⊢ φ` might end.

```lean
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
```

Soundness Continued
===

```lean
theorem sound_im_elim (h₁ : Γ ⊨ Formula.imp φ ψ) (h₂ : Γ ⊨ φ) : Γ ⊨ ψ := by
  intro α M a hΓ
  exact h₁ M a hΓ (h₂ M a hΓ)

theorem sound_all_intro (h : Formula.shift '' Γ ⊨ φ) : Γ ⊨ Formula.all φ := by
  intro α M a hΓ x
  exact h M (update a x) (fun χ hχ => by
    obtain ⟨ψ, hψ, rfl⟩ := hχ
    rw [show ψ.shift = ψ.rename (Var.shift 0) from rfl, satisfies_rename]
    exact hΓ ψ hψ)
```

Soundess Continued
===

```lean
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
```

Soundess Finished
===
And now the main result:

```lean
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
```

Completeness
===
Completness means `Γ ⊨ φ → Γ ⊢ φ`, which was proved by Gödel in 1929.

This theorem is more complex than soundness and at this point I have it only partially finished. Hopefully the next time I teach this course I'll have it done!



Incompleteness
===
Completeness is not to be confused with incompletness. Gödel showed the remarkable result that
```
∃ φ : Formula Nats, ¬(PA ⊢ φ) ∧ ¬(PA ⊢ Formula.not φ)
```

`PA` is the set of *Peano Axioms*:
```lean
1. ∀x, S(x) ≠ 0
2. ∀x ∀y, S(x) = S(y) → x = y
3. ∀x, x + 0 = x
4. ∀x ∀y, x + S(y) = S(x + y)
5. ∀x, x × 0 = 0
6. ∀x ∀y, x × S(y) = (x × y) + x
7. ∀ φ : Formula Nats, (φ(0) ∧ ∀x, φ(x) → φ(S(x))) → ∀x, φ(x)
```

GIT was proved by `Gödel` in 1931.

GIT appears to have been formalized [here](https://github.com/FormalizedFormalLogic). And a generalization, proved by Lawvere, is formalized in Agda [here](https://unimath.github.io/agda-unimath/foundation.lawveres-fixed-point-theorem.html).



Future Work
===

Spring 2026: Weekly research meetings on formalizing logic.


```lean
--hide
end
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

