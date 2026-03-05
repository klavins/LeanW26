
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

- A *partial* proof of **completness**: `Γ ⊢ φ → Γ ⊨ φ`

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
of the proof of the independence of the continuum hypothesis.




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



Variables
===
In first order logic we assume a countably infinite supply of variables `x₀`, `x₁`, `x₂`, ...,
which we identify with the natural numbers:

```lean
abbrev Var := ℕ
```
 We define a **substitution** of one variable for another as follows: 
```lean
def Var.subst (s x : Var) (v : Var) : Var :=
  if v = x then s else v

notation:max t "[" x " ↦ " s "]" => Var.subst s x t
```
 For example, 
```lean
namespace Examples
  example : 1[2↦1] = 1 := rfl
  example : 1[1↦2] = 2 := rfl
end Examples
```

Tuples
===

```lean
abbrev Arity := ℕ

abbrev Tuple (k : Arity) := Fin k → Var
```
 Tuples are easily expressed using Lean's `![...]` notation. For example, 
```lean
--hide
namespace Examples
--unhide

def my_tuple : Tuple 3 := ![1,2,3]

--hide
end Examples
--unhide
```

Formulas
===
The formulas of First Order Logic are defined in terms of a minimal set of connectives
and quantifiers, to keep proofs short.

```lean
abbrev Signature := Arity → Type

inductive Formula (S : Signature)
  | bot     : (Formula S)
  | rel {k} : S k → Tuple k  → (Formula S)
  | imp     : (Formula S) → (Formula S) → (Formula S)
  | all     : (Formula S) → (Formula S)
```

Derived Formulas
===
Other connectives and quantifiers are derived from the core syntax.

```lean
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
```

Example: Graphs
===
A signature `(E)` for directed graphs may be defined as follows

```lean
namespace Examples

inductive Graph : Signature
  | E   : Graph 2
  deriving Repr

open Formula Graph
```
 in which we can express the simple graph properties: 
```lean
def Graph.no_self_loops : Formula Graph :=
  all (not (rel E ![0,0]))

def Graph.completely_connected : Formula Graph :=
  all (all (rel E ![0,1]))
```

Example: Natural Numbers
===
A signature `(0,succ,+,*,≤)` for the natural numbers may be defined

```lean
inductive Nats : Signature
  | is_zero   : Nats 1
  | is_succ   : Nats 2
  | is_sum    : Nats 3
  | is_prod   : Nats 3
  | le        : Nats 2
  deriving Repr

open Nats
```
 in which we can represent various properties of the natural numbers: 
```lean
def Nats.one_plus_one := (Formula.and (rel is_zero ![0])
                         (Formula.and (rel is_succ ![0,1])
                         (Formula.and (rel is_succ ![1,2])
                         (rel is_sum ![1,1,2]))))
--hide
end Examples
--unhide
```

Exercises
===

<ex /> Define a formula over graphs stating that a graph has an isolated vertex.

<ex /> Define a formula over natural numnbers stating that a number is prime.

<ex /> Define a signature for Group Theory and define a formula stating that a group is Abelian.



Shifting and Instantiating
===
To support Debruijn indexing, variables need to be shifted up and down when
adding and removing quantifiers. We define the notion of a `level` to
define how far we are shifting.

```lean
abbrev Level := ℕ

def Var.shift (level : Level) (v : Var) : Var :=
  if v < level then v else v + 1

def Var.unshift (level : Level) (v : Var) : Var :=
  if v < level then v else v - 1
```

Instantiation
===

When a formula of the form `all φ` is instantiated at a particular term `t`
we replace occurances of `x₀` with `t`.

This is supported at the variable
level by the following:


```lean
def Var.inst_at (t : Var) (level : Level) (v : Var) : Var :=
  if v < level then v
  else if v = level then t
  else v - 1
```

Variable Substitution Properties
===
We define simplifiying theorems for variable substitution.

```lean
--hide
section
namespace Var
variable {level : Level} {t v s s' x y : Var}
--unhide

@[simp] theorem subst_eq : x[x↦s] = s := by simp[subst]

theorem subst_ne (h : t ≠ x) : t[x↦s] = t := by simp[subst, h]

@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : v[x↦s][y↦t] = v[y↦t][x↦s[y↦t]] := by <proofstate>['t v s x y : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ v[x ↦ s][y ↦ t] = v[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
  simp[subst] <proofstate>['t v s x y : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ (if (if v = x then s else v) = y then t else if v = x then s else v) =\n    if (if v = y then t else v) = x then if s = y then t else s else if v = y then t else v']</proofstate>
  aesop

@[simp] theorem subst_succ_ne_succ (h : t ≠ x)
  : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by <proofstate>['t s x : Var\nh : t ≠ x\n⊢ (t + 1)[x + 1 ↦ s + 1] = t[x ↦ s] + 1']</proofstate>
  simp[subst, h]

@[simp] theorem subst_succ : (t + 1)[x+1 ↦ s+1] = t[x↦s]+1 := by <proofstate>['t s x : Var\n⊢ (t + 1)[x + 1 ↦ s + 1] = t[x ↦ s] + 1']</proofstate>
  by_cases h : t = x <;> simp [h]
```

Variable Shifting and Instantiation Properties
===
To avoid having to do arithmetic and if-then-else reasoning in high level proofs, we prove a set of simplifiers for shifting and instantiating.

```lean
@[simp] theorem unshift_shift : unshift level ∘ shift level = id := by <proofstate>['level : Level\n⊢ unshift level ∘ shift level = id']</proofstate>
  --brief <proofstate>['level : Level\n⊢ unshift level ∘ shift level = id']</proofstate>
  funext v <proofstate>['case h\nlevel : Level\nv : Var\n⊢ (unshift level ∘ shift level) v = id v']</proofstate>
  simp[shift,unshift] <proofstate>['case h\nlevel : Level\nv : Var\n⊢ (if (if v < level then v else v + 1) < level then if v < level then v else v + 1\n    else (if v < level then v else v + 1) - 1) =\n    v']</proofstate>
  split_ifs with h1 h2 <proofstate>['case pos\nlevel : Level\nv : Var\nh1 : v < level\n⊢ v = v', 'case pos\nlevel : Level\nv : Var\nh1 : ¬v < level\nh2 : v + 1 < level\n⊢ v + 1 = v', 'case neg\nlevel : Level\nv : Var\nh1 : ¬v < level\nh2 : ¬v + 1 < level\n⊢ v + 1 - 1 = v']</proofstate>
  · rfl
  · have h3 : level < level := by <proofstate>['level : Level\nv : Var\nh1 : ¬v < level\nh2 : v + 1 < level\n⊢ level < level']</proofstate>
      have h4 : v < v + 1 := lt_add_one v <proofstate>['level : Level\nv : Var\nh1 : ¬v < level\nh2 : v + 1 < level\nh4 : v < v + 1\n⊢ level < level']</proofstate>
      have h5 : v < level := Nat.lt_trans h4 h2 <proofstate>['level : Level\nv : Var\nh1 : ¬v < level\nh2 : v + 1 < level\nh4 : v < v + 1\nh5 : v < level\n⊢ level < level']</proofstate>
      exact False.elim (h1 h5)
    exact False.elim ((lt_self_iff_false level).mp h3)
  · exact add_tsub_cancel_right _ _
  --unbrief

@[simp] theorem inst_at_lt (h : v < level) : inst_at t level v = v := by <proofstate>['level : Level\nt v : Var\nh : v < level\n⊢ t.inst_at level v = v']</proofstate>
  --brief <proofstate>['level : Level\nt v : Var\nh : v < level\n⊢ t.inst_at level v = v']</proofstate>
  simp [inst_at, h]
  --unbrief

@[simp] theorem inst_at_eq : inst_at t level level = t := by <proofstate>['level : Level\nt : Var\n⊢ t.inst_at level level = t']</proofstate>
  --brief <proofstate>['level : Level\nt : Var\n⊢ t.inst_at level level = t']</proofstate>
  simp [inst_at]
  --unbrief

@[simp] theorem inst_at_gt (h : level < v) : inst_at t level v = v - 1 := by <proofstate>['level : Level\nt v : Var\nh : level < v\n⊢ t.inst_at level v = v - 1']</proofstate>
  --brief <proofstate>['level : Level\nt v : Var\nh : level < v\n⊢ t.inst_at level v = v - 1']</proofstate>
  simp [inst_at, not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
  --unbrief

@[simp] theorem subst_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x ↦ s] = v := by <proofstate>['level : Level\nv s x : Var\nhv : v < level\nhx : level ≤ x\n⊢ v[x ↦ s] = v']</proofstate>
    --brief <proofstate>['level : Level\nv s x : Var\nhv : v < level\nhx : level ≤ x\n⊢ v[x ↦ s] = v']</proofstate>
   exact subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv hx))
  --unbrief

@[simp] theorem subst_succ_of_lt_of_le (hv : v < level) (hx : level ≤ x)
  : v[x+1 ↦ s+1] = v := by <proofstate>['level : Level\nv s x : Var\nhv : v < level\nhx : level ≤ x\n⊢ v[x + 1 ↦ s + 1] = v']</proofstate>
  --brief <proofstate>['level : Level\nv s x : Var\nhv : v < level\nhx : level ≤ x\n⊢ v[x + 1 ↦ s + 1] = v']</proofstate>
  exact subst_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hv (Nat.le_succ_of_le hx)))
  --unbrief
```

More simps
===

```lean
@[simp] theorem inst_at_succ_of_le (hs : level ≤ s) : inst_at t level (s + 1) = s := by <proofstate>['level : Level\nt s : Var\nhs : level ≤ s\n⊢ t.inst_at level (s + 1) = s']</proofstate>
  --brief <proofstate>['level : Level\nt s : Var\nhs : level ≤ s\n⊢ t.inst_at level (s + 1) = s']</proofstate>
  simp [inst_at_gt (Nat.lt_succ_of_le hs)]
  --unbrief

@[simp] theorem inst_at_shift : inst_at t level (Var.shift level v) = v := by <proofstate>['level : Level\nt v : Var\n⊢ t.inst_at level (shift level v) = v']</proofstate>
  --brief <proofstate>['level : Level\nt v : Var\n⊢ t.inst_at level (shift level v) = v']</proofstate>
  by_cases h : v < level <proofstate>['case pos\nlevel : Level\nt v : Var\nh : v < level\n⊢ t.inst_at level (shift level v) = v', 'case neg\nlevel : Level\nt v : Var\nh : ¬v < level\n⊢ t.inst_at level (shift level v) = v']</proofstate>
  · simp [Var.shift, h]
  · simp [Var.shift, h, inst_at_succ_of_le (Nat.le_of_not_lt h)]
  --unbrief

@[simp] theorem subst_pred_of_gt_of_ne (hgt : level < v) (hne : v ≠ x + 1)
  : (v - 1)[x ↦ s] = v - 1 := by <proofstate>['level : Level\nv s x : Var\nhgt : level < v\nhne : v ≠ x + 1\n⊢ (v - 1)[x ↦ s] = v - 1']</proofstate>
  --brief <proofstate>['level : Level\nv s x : Var\nhgt : level < v\nhne : v ≠ x + 1\n⊢ (v - 1)[x ↦ s] = v - 1']</proofstate>
  apply subst_ne <proofstate>['case h\nlevel : Level\nv s x : Var\nhgt : level < v\nhne : v ≠ x + 1\n⊢ v - 1 ≠ x']</proofstate>
  intro heq <proofstate>['case h\nlevel : Level\nv s x : Var\nhgt : level < v\nhne : v ≠ x + 1\nheq : v - 1 = x\n⊢ False']</proofstate>
  exact hne (Nat.eq_add_of_sub_eq (Nat.lt_of_le_of_lt (Nat.zero_le level) hgt) heq)
  --unbrief

theorem subst_inst_at (hs : level ≤ s) (hx : level ≤ x) :
    (inst_at t level v)[x ↦ s] =
    inst_at (t[x↦s]) level (v[x+1 ↦ s+1]) := by <proofstate>['level : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
  --brief <proofstate>['level : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
  by_cases h1 : v < level <proofstate>['case pos\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : v < level\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]', 'case neg\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
  · simp [subst_of_lt_of_le h1 hx, subst_succ_of_lt_of_le h1 hx, inst_at_lt h1]
  by_cases h2 : v = level <proofstate>['case pos\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : v = level\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]', 'case neg\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : ¬v = level\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
  · simp [*,subst_ne (Nat.ne_of_lt (hx.trans_lt (Nat.lt_succ_self x))), inst_at_eq]
  · have h3 : v ≥ level := Nat.le_of_not_lt h1 <proofstate>['case neg\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : ¬v = level\nh3 : v ≥ level\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
    have hgt : level < v := Nat.lt_of_le_of_ne h3 (Ne.symm h2) <proofstate>['case neg\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : ¬v = level\nh3 : v ≥ level\nhgt : level < v\n⊢ (t.inst_at level v)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
    rw [inst_at_gt hgt] <proofstate>['case neg\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : ¬v = level\nh3 : v ≥ level\nhgt : level < v\n⊢ (v - 1)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
    by_cases h4 : v = x + 1 <proofstate>['case pos\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : ¬v = level\nh3 : v ≥ level\nhgt : level < v\nh4 : v = x + 1\n⊢ (v - 1)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]', 'case neg\nlevel : Level\nt v s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬v < level\nh2 : ¬v = level\nh3 : v ≥ level\nhgt : level < v\nh4 : ¬v = x + 1\n⊢ (v - 1)[x ↦ s] = t[x ↦ s].inst_at level v[x + 1 ↦ s + 1]']</proofstate>
    · subst h4 <proofstate>['case pos\nlevel : Level\nt s x : Var\nhs : level ≤ s\nhx : level ≤ x\nh1 : ¬x + 1 < level\nh2 : ¬x + 1 = level\nh3 : x + 1 ≥ level\nhgt : level < x + 1\n⊢ (x + 1 - 1)[x ↦ s] = t[x ↦ s].inst_at level (x + 1)[x + 1 ↦ s + 1]']</proofstate>
      simp [subst_eq, inst_at_succ_of_le hs]
    · rw [subst_pred_of_gt_of_ne hgt h4, subst_ne h4, inst_at_gt hgt]
  --unbrief

--hide
end Var
end
--unhide
```

Extending to Tuples
===

By composing variable operators with tuples, we can lift the standard
operations to tuples. Subsitution is simply:

```lean
def Tuple.subst {k} (s x : Var) (tuple : Tuple k) : Tuple k :=
  (Var.subst s x) ∘ tuple

notation:max t "[" x " ↦ " s "]" => Tuple.subst s x t
```
 And the other operations are 
```lean
def Tuple.shift {k} (level : Level) (tuple : Tuple k): Tuple k :=
  (Var.shift level) ∘ tuple

def Tuple.unshift {k} (level : Level) (tuple : Tuple k): Tuple k :=
  (Var.unshift level) ∘ tuple

def Tuple.inst_at {k} (level : Level) (t : Var) (tuple : Tuple k) : Tuple k :=
  (Var.inst_at t level) ∘ tuple
```

Theorems About Tuples
===
We similarly have a number of `@[simps]` for `Tuple`.

```lean
--hide
section
namespace Tuple
variable {k : Arity} {level : Level} {s t x y : Var} {τ : Tuple k} {i : Fin k}
--unhide

@[simp] theorem unshift_shift
  : (unshift (k := k) level) ∘ (shift (k := k) level) = id := by <proofstate>['k : Arity\nlevel : Level\n⊢ unshift level ∘ shift level = id']</proofstate>
  --brief <proofstate>['k : Arity\nlevel : Level\n⊢ unshift level ∘ shift level = id']</proofstate>
  funext tuple <proofstate>['case h\nk : Arity\nlevel : Level\ntuple : Tuple k\n⊢ (unshift level ∘ shift level) tuple = id tuple']</proofstate>
  simp[unshift,shift,←Function.comp_assoc]
  --unbrief

@[simp] theorem subst_apply
  : τ[x↦s] i = ((τ i)[x↦s]:Var) := rfl

@[simp] theorem inst_at_apply
  : inst_at level t τ i = Var.inst_at t level (τ i) := rfl

@[simp] theorem inst_at_shift
  : inst_at level t (shift level τ) = τ := by <proofstate>['k : Arity\nlevel : Level\nt : Var\nτ : Tuple k\n⊢ inst_at level t (shift level τ) = τ']</proofstate>
  --brief <proofstate>['k : Arity\nlevel : Level\nt : Var\nτ : Tuple k\n⊢ inst_at level t (shift level τ) = τ']</proofstate>
  funext i <proofstate>['case h\nk : Arity\nlevel : Level\nt : Var\nτ : Tuple k\ni : Fin k\n⊢ inst_at level t (shift level τ) i = τ i']</proofstate>
  simp [shift, Var.inst_at_shift]
  --unbrief

@[simp] theorem inst_at_subst (hs : level ≤ s) (hx : level ≤ x) :
  (inst_at level t τ)[x↦s] = (τ[x+1↦s+1]).inst_at level (t[x↦s]) := by <proofstate>['k : Arity\nlevel : Level\ns t x : Var\nτ : Tuple k\nhs : level ≤ s\nhx : level ≤ x\n⊢ (inst_at level t τ)[x ↦ s] = inst_at level t[x ↦ s] τ[x + 1 ↦ s + 1]']</proofstate>
  --brief <proofstate>['k : Arity\nlevel : Level\ns t x : Var\nτ : Tuple k\nhs : level ≤ s\nhx : level ≤ x\n⊢ (inst_at level t τ)[x ↦ s] = inst_at level t[x ↦ s] τ[x + 1 ↦ s + 1]']</proofstate>
  funext i <proofstate>['case h\nk : Arity\nlevel : Level\ns t x : Var\nτ : Tuple k\nhs : level ≤ s\nhx : level ≤ x\ni : Fin k\n⊢ (inst_at level t τ)[x ↦ s] i = inst_at level t[x ↦ s] τ[x + 1 ↦ s + 1] i']</proofstate>
  simp only [Tuple.subst, Tuple.inst_at, Function.comp] <proofstate>['case h\nk : Arity\nlevel : Level\ns t x : Var\nτ : Tuple k\nhs : level ≤ s\nhx : level ≤ x\ni : Fin k\n⊢ (t.inst_at level (τ i))[x ↦ s] = t[x ↦ s].inst_at level (τ i)[x + 1 ↦ s + 1]']</proofstate>
  exact Var.subst_inst_at hs hx
  --unbrief
```

More Theorems about Tuples
===
And last but not least:

```lean
@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : τ[x↦s][y↦t] = τ[y↦t][x↦s[y↦t]] := by <proofstate>['k : Arity\ns t x y : Var\nτ : Tuple k\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ τ[x ↦ s][y ↦ t] = τ[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
  --brief <proofstate>['k : Arity\ns t x y : Var\nτ : Tuple k\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ τ[x ↦ s][y ↦ t] = τ[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
  simp[subst,h₁,h₂,funext_iff]
  --unbrief

@[simp] theorem subst_id : τ[x↦x] = τ := by <proofstate>['k : Arity\nx : Var\nτ : Tuple k\n⊢ τ[x ↦ x] = τ']</proofstate>
  --brief <proofstate>['k : Arity\nx : Var\nτ : Tuple k\n⊢ τ[x ↦ x] = τ']</proofstate>
  simp[subst,funext_iff,Var.subst] <proofstate>['k : Arity\nx : Var\nτ : Tuple k\n⊢ ∀ (x_1 : Fin k), τ x_1 = x → x = τ x_1']</proofstate>
  intro _ hi <proofstate>['k : Arity\nx : Var\nτ : Tuple k\nx✝ : Fin k\nhi : τ x✝ = x\n⊢ x = τ x✝']</proofstate>
  exact Eq.symm hi
  --unbrief
```
 While the `Var` simples are tedious and tricky, the `Tuple` proofs are easy extensions. 
```lean
--hide
end Tuple
end
--unhide
```

Exercises
===

<ex /> Show that substituting `x` for `y` and then `y` for `x` in a tuple does not necessarily result in the same tuple.



Substitution on Formulas
===
Substitution on formulas is defined inductively.

```lean
def Formula.subst {S : Signature} (t : Var) (x : Var) : Formula S → Formula S
  | bot => bot
  | rel r tuple => rel r (Tuple.subst t x tuple)
  | imp φ ψ => imp (subst t x φ) (subst t x ψ)
  | all φ => all (subst (t+1) (x+1) φ)

notation:max φ "[" x " ↦ " s "]" => Formula.subst s x φ
```
 For example: 
```lean
--hide
namespace Examples
--unhide

def Nats.one_plus_one_alt := Nats.one_plus_one[2↦3]
```
 results in a formula where the variable `x₃` represents `2` instead
of `x₂` representing `2`.
```lean
--hide
end Examples
--unhide
```

Subtitution simps
===
The following substutition `@[simps]` make subsequent proofs much easier.

```lean
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
@[simp] theorem subst_rel0 : (rel r₁ ![0])[0↦s] = rel r₁ ![s] := by <proofstate>['S : Signature\ns : Var\nr₁ : S 1\n⊢ (rel r₁ ![0])[0 ↦ s] = rel r₁ ![s]']</proofstate>
  --brief <proofstate>['S : Signature\ns : Var\nr₁ : S 1\n⊢ (rel r₁ ![0])[0 ↦ s] = rel r₁ ![s]']</proofstate>
  simp[funext_iff]
  --unbrief
@[simp] theorem subst_rel0' : (rel r₁) ![0][0↦s]  = rel r₁ ![s] := by <proofstate>['S : Signature\ns : Var\nr₁ : S 1\n⊢ rel r₁ ![0][0 ↦ s] = rel r₁ ![s]']</proofstate>
  --brief <proofstate>['S : Signature\ns : Var\nr₁ : S 1\n⊢ rel r₁ ![0][0 ↦ s] = rel r₁ ![s]']</proofstate>
  simp[funext_iff]
  --unbrief

--hide
end Formula
end
--unhide
```

Renamers
===

Next we define an infrastructure that can be used to rename all free variables in a formula.


```lean
abbrev Renamer := Var → Var

def Renamer.lift (f : Renamer) : Renamer
  | 0 => 0
  | n+1 => (f n) + 1
--hide
section
variable {f g : Renamer} {level : Level}
--unhide
@[simp] theorem Renamer.lift_id : lift id = id := by <proofstate>['⊢ lift id = id']</proofstate>
  --brief <proofstate>['⊢ lift id = id']</proofstate>
  funext i <proofstate>['case h\ni : Var\n⊢ lift id i = id i']</proofstate>
  simp[lift] <proofstate>['case h\ni : Var\n⊢ (match i with\n    | 0 => 0\n    | Nat.succ n => n + 1) =\n    i']</proofstate>
  cases i <;> rfl
  --unbrief

@[simp] theorem Renamer.lift_comp : lift (g ∘ f) = lift g ∘ lift f := by <proofstate>['f g : Renamer\n⊢ lift (g ∘ f) = g.lift ∘ f.lift']</proofstate>
  --brief <proofstate>['f g : Renamer\n⊢ lift (g ∘ f) = g.lift ∘ f.lift']</proofstate>
  funext i <proofstate>['case h\nf g : Renamer\ni : Var\n⊢ lift (g ∘ f) i = (g.lift ∘ f.lift) i']</proofstate>
  simp[lift] <proofstate>['case h\nf g : Renamer\ni : Var\n⊢ (match i with\n    | 0 => 0\n    | Nat.succ n => g (f n) + 1) =\n    match\n      match i with\n      | 0 => 0\n      | Nat.succ n => f n + 1 with\n    | 0 => 0\n    | Nat.succ n => g n + 1']</proofstate>
  cases i <;> rfl
  --unbrief

@[simp] theorem Renamer.lift_shift
  : lift f ∘ Var.shift 0 = Var.shift 0 ∘ f := by <proofstate>['f : Renamer\n⊢ f.lift ∘ Var.shift 0 = Var.shift 0 ∘ f']</proofstate>
  --brief <proofstate>['f : Renamer\n⊢ f.lift ∘ Var.shift 0 = Var.shift 0 ∘ f']</proofstate>
  funext i <proofstate>['case h\nf : Renamer\ni : Var\n⊢ (f.lift ∘ Var.shift 0) i = (Var.shift 0 ∘ f) i']</proofstate>
  simp[lift] <proofstate>['case h\nf : Renamer\ni : Var\n⊢ (match Var.shift 0 i with\n    | 0 => 0\n    | Nat.succ n => f n + 1) =\n    Var.shift 0 (f i)']</proofstate>
  rfl
  --unbrief

@[simp] theorem hlift : Renamer.lift (Var.shift level)
                        = Var.shift (level + 1) := by <proofstate>['level : Level\n⊢ Renamer.lift (Var.shift level) = Var.shift (level + 1)']</proofstate>
  --brief <proofstate>['level : Level\n⊢ Renamer.lift (Var.shift level) = Var.shift (level + 1)']</proofstate>
    funext v <proofstate>['case h\nlevel : Level\nv : Var\n⊢ Renamer.lift (Var.shift level) v = Var.shift (level + 1) v']</proofstate>
    cases v <proofstate>['case h.zero\nlevel : Level\n⊢ Renamer.lift (Var.shift level) Nat.zero = Var.shift (level + 1) Nat.zero', 'case h.succ\nlevel : Level\nn✝ : ℕ\n⊢ Renamer.lift (Var.shift level) n✝.succ = Var.shift (level + 1) n✝.succ']</proofstate>
    · simp [Renamer.lift, Var.shift]
    · simp only [Renamer.lift, Var.shift, Nat.succ_lt_succ_iff] <proofstate>['case h.succ\nlevel : Level\nn✝ : ℕ\n⊢ (if n✝ < level then n✝ else n✝ + 1) + 1 = if n✝ < level then n✝.succ else n✝.succ + 1']</proofstate>
      split_ifs <;> rfl
  --unbrief

--hide
end
--unhide
```

Rename
===
We now define renaming for formulas

```lean
def Formula.rename {S : Signature} (φ : Formula S) (f : Renamer) : Formula S :=
  match φ with
    | bot => bot
    | rel r t => rel r (f ∘ t)
    | imp ψ₁ ψ₂ => imp (rename ψ₁ f) (rename ψ₂ f)
    | all ψ => all (rename ψ (f.lift))
```
 And associated @simps 
```lean
--hide
section
open Formula
variable {S : Signature} {φ : Formula S} {f g : Renamer} {t : Var} {level : Level}
--unhide

@[simp] theorem rename_id : φ.rename id = φ := by <proofstate>['S : Signature\nφ : Formula S\n⊢ φ.rename id = φ']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\n⊢ φ.rename id = φ']</proofstate>
  induction φ with <proofstate>['S : Signature\nφ : Formula S\n⊢ φ.rename id = φ']</proofstate>
  | bot => rfl
  | rel r t => simp [rename]
  | imp ψ₁ ψ₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]
  | all ψ ih => simp [rename, ih]
  --unbrief

@[simp] theorem rename_comp
  : (φ.rename f).rename g = φ.rename (g ∘ f) := by <proofstate>['S : Signature\nφ : Formula S\nf g : Renamer\n⊢ (φ.rename f).rename g = φ.rename (g ∘ f)']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\nf g : Renamer\n⊢ (φ.rename f).rename g = φ.rename (g ∘ f)']</proofstate>
  induction φ generalizing f g with <proofstate>['S : Signature\nφ : Formula S\nf g : Renamer\n⊢ (φ.rename f).rename g = φ.rename (g ∘ f)']</proofstate>
  | bot => rfl
  | rel r t => simp [rename, Function.comp_assoc]
  | imp ψ₁ ψ₂ ih₁ ih₂ => simp [rename, ih₁, ih₂]
  | all ψ ih => simp [rename, ih]
  --unbrief

@[simp] theorem lift_inst_at  :
    Renamer.lift (Var.inst_at t level) =
    Var.inst_at (t+1) (level+1) := by <proofstate>['t : Var\nlevel : Level\n⊢ Renamer.lift (t.inst_at level) = (t + 1).inst_at (level + 1)']</proofstate>
  --brief <proofstate>['t : Var\nlevel : Level\n⊢ Renamer.lift (t.inst_at level) = (t + 1).inst_at (level + 1)']</proofstate>
  funext v <proofstate>['case h\nt : Var\nlevel : Level\nv : Var\n⊢ Renamer.lift (t.inst_at level) v = (t + 1).inst_at (level + 1) v']</proofstate>
  cases v with <proofstate>['case h\nt : Var\nlevel : Level\nv : Var\n⊢ Renamer.lift (t.inst_at level) v = (t + 1).inst_at (level + 1) v']</proofstate>
  | zero => simp [Renamer.lift, Var.inst_at]
  | succ n => <proofstate>['case h.succ\nt : Var\nlevel : Level\nn : ℕ\n⊢ Renamer.lift (t.inst_at level) n.succ = (t + 1).inst_at (level + 1) n.succ']</proofstate>
     simp[Renamer.lift, Var.inst_at] <proofstate>['case h.succ\nt : Var\nlevel : Level\nn : ℕ\n⊢ (if n < level then n else if n = level then t else n - 1) + 1 =\n    if n < level then n + 1 else if n = level then t + 1 else n']</proofstate>
     split_ifs <proofstate>['case pos\nt : Var\nlevel : Level\nn : ℕ\nh✝ : n < level\n⊢ n + 1 = n + 1', 'case pos\nt : Var\nlevel : Level\nn : ℕ\nh✝¹ : ¬n < level\nh✝ : n = level\n⊢ t + 1 = t + 1', 'case neg\nt : Var\nlevel : Level\nn : ℕ\nh✝¹ : ¬n < level\nh✝ : ¬n = level\n⊢ n - 1 + 1 = n']</proofstate>
     · simp
     · simp
     · apply Nat.succ_pred_eq_of_ne_zero <proofstate>['case neg.a\nt : Var\nlevel : Level\nn : ℕ\nh✝¹ : ¬n < level\nh✝ : ¬n = level\n⊢ n.sub 0 ≠ 0']</proofstate>
       aesop
  --unbrief

--hide
end
--unhide
```

Instantiation for Formulas
===
Applying a formula of the form `all φ` to a particular term `t` is called instantiating `φ` with `t`.

We define a general notion of instantition at any level.

```lean
open Formula in
def Formula.inst_at {S : Signature} (t : Var) (level : Level)
  : Formula S → Formula S
  | bot         => bot
  | rel r tuple => rel r (tuple.inst_at level t)
  | imp φ ψ     => imp (inst_at t level φ) (inst_at t level ψ)
  | all φ       => all (inst_at (t+1) (level+1) φ)
```
 And then we define instantiation at `0`. 
```lean
def Formula.inst {S : Signature} (t : Var) : Formula S → Formula S :=
  inst_at t 0
```

Instantiation Example
===

For example, instantiating `∀ x . E(x,y)` with `z` gives `∀ x . E(x,z)`.

The the example below, we use `10` for `z`.


```lean
--hide
namespace Examples
--unhide

open Graph Formula

example : (all (rel E ![0,1])).inst 10
        = (all (rel E ![0,11])) := by <proofstate>['⊢ inst 10 (rel E ![0, 1]).all = (rel E ![0, 11]).all']</proofstate>
  simp[inst,inst_at,Tuple.inst_at,funext_iff,Var.inst_at]

--hide
end Examples
--unhide
```

Instantiation simps
===
We prove a number of results about instantiation.

```lean
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
@[simp] theorem subst_id : φ[x↦x] = φ := by <proofstate>['S : Signature\nφ : Formula S\nx : Var\n⊢ φ[x ↦ x] = φ']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\nx : Var\n⊢ φ[x ↦ x] = φ']</proofstate>
  induction φ generalizing x <;> simp[*]
  --unbrief

theorem inst_at_subst (h₁ : L ≤ x) (h₂ : L ≤ s)
  : (φ.inst_at t L)[x↦s] = φ[x+1↦s+1].inst_at t[x↦s] L := by <proofstate>['S : Signature\nφ : Formula S\ns x t : Var\nL : Level\nh₁ : L ≤ x\nh₂ : L ≤ s\n⊢ (inst_at t L φ)[x ↦ s] = inst_at t[x ↦ s] L φ[x + 1 ↦ s + 1]']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\ns x t : Var\nL : Level\nh₁ : L ≤ x\nh₂ : L ≤ s\n⊢ (inst_at t L φ)[x ↦ s] = inst_at t[x ↦ s] L φ[x + 1 ↦ s + 1]']</proofstate>
  induction φ generalizing t s L x with <proofstate>['S : Signature\nφ : Formula S\ns x t : Var\nL : Level\nh₁ : L ≤ x\nh₂ : L ≤ s\n⊢ (inst_at t L φ)[x ↦ s] = inst_at t[x ↦ s] L φ[x + 1 ↦ s + 1]']</proofstate>
  | bot => rfl
  | rel t τ => simp[*]
  | imp f g ihf ihg => simp[*]
  | all f ih => <proofstate>['case all\nS : Signature\nf : Formula S\nih : ∀ {s x t : Var} {L : Level}, L ≤ x → L ≤ s → (inst_at t L f)[x ↦ s] = inst_at t[x ↦ s] L f[x + 1 ↦ s + 1]\ns x t : Var\nL : Level\nh₁ : L ≤ x\nh₂ : L ≤ s\n⊢ (inst_at t L f.all)[x ↦ s] = inst_at t[x ↦ s] L f.all[x + 1 ↦ s + 1]']</proofstate>
      simp [ih (Nat.succ_le_succ h₁) (Nat.succ_le_succ h₂)]
  --unbrief

theorem inst_subst {S : Signature} (φ : Formula S) (s x t : Var)
  : (φ.inst t)[x↦s] = φ[x+1↦s+1].inst t[x↦s]  := by <proofstate>['S : Signature\nφ : Formula S\ns x t : Var\n⊢ (inst t φ)[x ↦ s] = inst t[x ↦ s] φ[x + 1 ↦ s + 1]']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\ns x t : Var\n⊢ (inst t φ)[x ↦ s] = inst t[x ↦ s] φ[x + 1 ↦ s + 1]']</proofstate>
  exact inst_at_subst (Nat.zero_le x) (Nat.zero_le s)
  --unbrief
```

Example Proof
===
Most of these proofs are simple. Here's a slightly complicated one:

```lean
@[simp] theorem subst_subst (h₁ : x ≠ y) (h₂ : t ≠ x)
  : φ[x↦s][y↦t] = φ[y↦t][x↦s[y↦t]] := by <proofstate>['S : Signature\nφ : Formula S\ns x y t : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ φ[x ↦ s][y ↦ t] = φ[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
  induction φ generalizing t s x y with <proofstate>['S : Signature\nφ : Formula S\ns x y t : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ φ[x ↦ s][y ↦ t] = φ[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
  | bot => rfl
  | rel r τ => simp[subst, *]
  | imp f g ihf ihg => simp[subst, *]
  | all f ih => <proofstate>['case all\nS : Signature\nf : Formula S\nih : ∀ {s x y t : Var}, x ≠ y → t ≠ x → f[x ↦ s][y ↦ t] = f[y ↦ t][x ↦ s[y ↦ t]]\ns x y t : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\n⊢ f.all[x ↦ s][y ↦ t] = f.all[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
    have := @ih (s+1) (x+1) (y+1) (t+1) <proofstate>['case all\nS : Signature\nf : Formula S\nih : ∀ {s x y t : Var}, x ≠ y → t ≠ x → f[x ↦ s][y ↦ t] = f[y ↦ t][x ↦ s[y ↦ t]]\ns x y t : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\nthis : f[x + 1 ↦ s + 1][y + 1 ↦ t + 1] = f[y + 1 ↦ t + 1][x + 1 ↦ (s + 1)[y + 1 ↦ t + 1]]\n⊢ f.all[x ↦ s][y ↦ t] = f.all[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
                ((add_ne_add_left 1).mpr h₁) <proofstate>['case all\nS : Signature\nf : Formula S\nih : ∀ {s x y t : Var}, x ≠ y → t ≠ x → f[x ↦ s][y ↦ t] = f[y ↦ t][x ↦ s[y ↦ t]]\ns x y t : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\nthis : f[x + 1 ↦ s + 1][y + 1 ↦ t + 1] = f[y + 1 ↦ t + 1][x + 1 ↦ (s + 1)[y + 1 ↦ t + 1]]\n⊢ f.all[x ↦ s][y ↦ t] = f.all[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
                ((add_ne_add_left 1).mpr h₂) <proofstate>['case all\nS : Signature\nf : Formula S\nih : ∀ {s x y t : Var}, x ≠ y → t ≠ x → f[x ↦ s][y ↦ t] = f[y ↦ t][x ↦ s[y ↦ t]]\ns x y t : Var\nh₁ : x ≠ y\nh₂ : t ≠ x\nthis : f[x + 1 ↦ s + 1][y + 1 ↦ t + 1] = f[y + 1 ↦ t + 1][x + 1 ↦ (s + 1)[y + 1 ↦ t + 1]]\n⊢ f.all[x ↦ s][y ↦ t] = f.all[y ↦ t][x ↦ s[y ↦ t]]']</proofstate>
    simp[this]
```

Exercises
===

<ex /> Show that `subst_subst` is not necessariy true when if we drop the requirement that `x ≠ y`.



Shifting
===

We now start building the definition of provability, starting with shifting.

Shifting is renaming by shifting at `0`. It is used in the definition of `∀-Intro`:

```lean
def shift {S : Signature} (φ : Formula S) := φ.rename (Var.shift 0)
```
 The interaction between instantiation and shift is a key property. 
```lean
@[simp] theorem inst_shift : (φ.shift).inst x = φ := by <proofstate>['S : Signature\nφ : Formula S\nx : Var\n⊢ inst x φ.shift = φ']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\nx : Var\n⊢ inst x φ.shift = φ']</proofstate>
  suffices h : ∀ (level : Level), (φ.rename (Var.shift level)).inst_at x level = φ from h 0 <proofstate>['S : Signature\nφ : Formula S\nx : Var\n⊢ ∀ (level : Level), inst_at x level (φ.rename (Var.shift level)) = φ']</proofstate>
  induction φ generalizing x with <proofstate>['S : Signature\nφ : Formula S\nx : Var\n⊢ ∀ (level : Level), inst_at x level (φ.rename (Var.shift level)) = φ']</proofstate>
  | bot => intros; rfl
  | rel r τ => <proofstate>['case rel\nS : Signature\nk✝ : Arity\nr : S k✝\nτ : Tuple k✝\nx : Var\n⊢ ∀ (level : Level), inst_at x level ((rel r τ).rename (Var.shift level)) = rel r τ']</proofstate>
    intros <proofstate>['case rel\nS : Signature\nk✝ : Arity\nr : S k✝\nτ : Tuple k✝\nx : Var\nlevel✝ : Level\n⊢ inst_at x level✝ ((rel r τ).rename (Var.shift level✝)) = rel r τ']</proofstate>
    simp [rename] <proofstate>['case rel\nS : Signature\nk✝ : Arity\nr : S k✝\nτ : Tuple k✝\nx : Var\nlevel✝ : Level\n⊢ Tuple.inst_at level✝ x (Var.shift level✝ ∘ τ) = τ']</proofstate>
    exact Tuple.inst_at_shift
  | imp f g ihf ihg => simp [rename, ihf, ihg]
  | all f ih => simp [rename, ih]
  --unbrief

theorem inst_at_eq_rename
  : φ.inst_at t L = φ.rename (Var.inst_at t L) := by <proofstate>['S : Signature\nφ : Formula S\nt : Var\nL : Level\n⊢ inst_at t L φ = φ.rename (t.inst_at L)']</proofstate>
  --brief <proofstate>['S : Signature\nφ : Formula S\nt : Var\nL : Level\n⊢ inst_at t L φ = φ.rename (t.inst_at L)']</proofstate>
  induction φ generalizing t L with <proofstate>['S : Signature\nφ : Formula S\nt : Var\nL : Level\n⊢ inst_at t L φ = φ.rename (t.inst_at L)']</proofstate>
  | bot => rfl
  | rel r τ => simp[Formula.inst_at, Formula.rename, Tuple.inst_at]
  | imp g h ihg ihh => simp[Formula.inst_at, Formula.rename, ihg, ihh]
  | all g ih => <proofstate>['case all\nS : Signature\ng : Formula S\nih : ∀ {t : Var} {L : Level}, inst_at t L g = g.rename (t.inst_at L)\nt : Var\nL : Level\n⊢ inst_at t L g.all = g.all.rename (t.inst_at L)']</proofstate>
    simp only [Formula.inst_at, Formula.rename] <proofstate>['case all\nS : Signature\ng : Formula S\nih : ∀ {t : Var} {L : Level}, inst_at t L g = g.rename (t.inst_at L)\nt : Var\nL : Level\n⊢ (inst_at (t + 1) (L + 1) g).all = (g.rename (Renamer.lift (t.inst_at L))).all']</proofstate>
    simp[lift_inst_at] <proofstate>['case all\nS : Signature\ng : Formula S\nih : ∀ {t : Var} {L : Level}, inst_at t L g = g.rename (t.inst_at L)\nt : Var\nL : Level\n⊢ inst_at (t + 1) (L + 1) g = g.rename ((t + 1).inst_at (L + 1))']</proofstate>
    exact ih
  --unbrief
```
 Both of these proofs require proof by induction un the structure of the formula. 
```lean
--hide
end Formula
end
--unhide
```

Provability
===

```lean
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
```

Provability Example
===
To illustrate the how proofs work in this system, we do a few proofs.

```lean
--hide
namespace Examples
open Formula Provable
--unhide
```
 Now we can do proofs like this one showing `(∀ x, P x) → (∀ x. Px)`. 
```lean
example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (all (rel P ![0])) := by <proofstate>['S : Signature\nP : S 1\n⊢ ∅ ⊢ (rel P ![0]).all.imp (rel P ![0]).all']</proofstate>
  apply im_intro <proofstate>['case a\nS : Signature\nP : S 1\n⊢ ∅ ∪ {(rel P ![0]).all} ⊢ (rel P ![0]).all']</proofstate>
  apply ax <proofstate>['case a.h\nS : Signature\nP : S 1\n⊢ (rel P ![0]).all ∈ ∅ ∪ {(rel P ![0]).all}']</proofstate>
  simp
```

Another Example
===
Here we show
```
∅ ⊢ ∀x, P(x) → P(5)
```
to test `all_elim` 
```lean
example {S : Signature} {P : S 1}
  : ∅ ⊢ imp (all (rel P ![0])) (rel P ![5]) := by <proofstate>['S : Signature\nP : S 1\n⊢ ∅ ⊢ (rel P ![0]).all.imp (rel P ![5])']</proofstate>
  apply im_intro <proofstate>['case a\nS : Signature\nP : S 1\n⊢ ∅ ∪ {(rel P ![0]).all} ⊢ rel P ![5]']</proofstate>
  have : rel P ![5] = (rel P ![0]).inst 5 := by <proofstate>['S : Signature\nP : S 1\n⊢ rel P ![5] = inst 5 (rel P ![0])']</proofstate>
    simp[Tuple.inst_at,funext_iff]
  rw[this] <proofstate>['case a\nS : Signature\nP : S 1\nthis : rel P ![5] = inst 5 (rel P ![0])\n⊢ ∅ ∪ {(rel P ![0]).all} ⊢ inst 5 (rel P ![0])']</proofstate>
  apply all_elim <proofstate>['case a.a\nS : Signature\nP : S 1\nthis : rel P ![5] = inst 5 (rel P ![0])\n⊢ ∅ ∪ {(rel P ![0]).all} ⊢ (rel P ![0]).all']</proofstate>
  apply ax <proofstate>['case a.a.h\nS : Signature\nP : S 1\nthis : rel P ![5] = inst 5 (rel P ![0])\n⊢ (rel P ![0]).all ∈ ∅ ∪ {(rel P ![0]).all}']</proofstate>
  simp

--hide
end Examples
--unhide
```

Exercises
===

<ex /> Show the following:


```lean
section
namespace Examples

  open Formula Provable

  example {S : Signature} {P Q : S 1}
    : {all (all (rel P ![0]))} ⊢ rel P ![3] := by <proofstate>['S : Signature\nP Q : S 1\n⊢ {(rel P ![0]).all.all} ⊢ rel P ![3]']</proofstate>
    sorry

end Examples
end
```

Models
===
While the AST and provability define a syntax, a
**model** defines a universe over which variables live, and a
**semantics** for each predicate in a signature.

```lean
universe u

structure Model (S : Signature) (α : Type u) where
  interp {arity} : S arity → (Fin arity → α) → Prop
```
 For example, here is a model of a simple signature. 
```lean
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
```

Assignments
===
An **assignment** is a function from variables to values of some type `α`.

```lean
def Assignment (α : Type u) := Var → α
```
 We operate on assignments with the following. 
```lean
def update {α : Type u} (A : Assignment α) (v : α) : Assignment α :=
  fun j => if j = 0 then v else A (j-1)

def update_at {α : Type u} (x : Var) (v : α) (A : Assignment α) : Assignment α :=
  fun j => if j = x then v else A j

def inst_assign {α : Type u} (A : Assignment α) (t : Var) (L : Level)
  : Assignment α := fun j => if      j < L then A j
                             else if j = L then A t
                             else               A (j - 1)
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
 We define *models* as satisfaction under any assignment. 
```lean
def models {S : Signature} {α : Type u} (M : Model S α) (f : Formula S) :=
  ∀ a, satisfies M a f
```

Example
===
Define a cyclic graph:

```lean
--hide
namespace Examples
open Graph
--unhide

def Cycle (n : ℕ) : Model Graph (Fin n) := ⟨
  fun sym tuple => match sym with
  | E => tuple 0 = ((tuple 1) + 1) % n ⟩
```
 The a cycle with one node has one (and only one) self loop 
```lean
example : ¬models (Cycle 1) Graph.no_self_loops := by <proofstate>['⊢ ¬models (Cycle 1) no_self_loops']</proofstate>
  intro h <proofstate>['h : models (Cycle 1) no_self_loops\n⊢ False']</proofstate>
  have := h (fun _ => 0) <proofstate>['h : models (Cycle 1) no_self_loops\nthis : satisfies (Cycle 1) (fun x ↦ 0) no_self_loops\n⊢ False']</proofstate>
  simp[no_self_loops,Formula.not,satisfies,Cycle] at this
```
 While a cycle with two nodes does not: 
```lean
example : models (Cycle 2) Graph.no_self_loops := by <proofstate>['⊢ models (Cycle 2) no_self_loops']</proofstate>
  intro A v h <proofstate>['A : Assignment (Fin 2)\nv : Fin 2\nh : satisfies (Cycle 2) (update A v) (Formula.rel E ![0, 0])\n⊢ satisfies (Cycle 2) (update A v) Formula.bot']</proofstate>
  fin_cases v <;> simp_all[satisfies,Cycle,update]

--hide
end Examples
--unhide
```

Exercise
===

<ex /> Define a Model for the signature `Nats` with the usual definition of
`zero`, `succ`, `add`, `prod`, and `le`.

<ex /> Show the model satisfies `Nats.one_plus_one`.



Entailment
===
A context `Γ` entails a formula `φ` if for all models `M` and assignments `A`, if
`M` and `A` satisfy every formula in `Γ`, then `M` and `A` satisfy `φ`.

```lean
def entails {S : Signature} (Γ : Context S) (φ : Formula S) : Prop :=
 ∀ {β : Type} (M : Model S β) (A : Assignment β),
 (∀ ψ ∈ Γ, satisfies M A ψ) → satisfies M A φ

infix:25 " ⊨ " => entails
```
 For example, 
```lean
--hide
namespace Examples
open Graph Formula
--unhide

example {S : Signature} {P : S 1}
  : ∅ ⊨ imp (rel P ![0]) (rel P ![0]) := by <proofstate>['S : Signature\nP : S 1\n⊢ ∅ ⊨ (rel P ![0]).imp (rel P ![0])']</proofstate>
  intro β M A h1 h2 <proofstate>['S : Signature\nP : S 1\nβ : Type\nM : Model S β\nA : Assignment β\nh1 : ∀ ψ ∈ ∅, satisfies M A ψ\nh2 : satisfies M A (rel P ![0])\n⊢ satisfies M A (rel P ![0])']</proofstate>
  exact h2

--hide
end Examples
--unhide
```

<div class='fn'>
In the definition of entails, <tt>β : Type</tt> instead of <tt>β : Type v</tt>.
Unfortunately, Lean doesn't support universe quantification inside <tt>Prop</tt>.
I can't figure out a way around this.
</div>



Theorems about Satisfies
===
We prove the follow help theorems about satisfaction and how it interacts with
lifting, renaming and instantiation.

```lean
--hide
variable {α : Type u} {S : Signature} {Γ : Context S} {M : Model S α}
         {φ ψ : Formula S} {a : Assignment α} {x : α} {f : Renamer}
         {t : Var} {level : Level}
--unhide

theorem update_comp_lift : update a x ∘ f.lift = update (a ∘ f) x := by <proofstate>['α : Type u\na : Assignment α\nx : α\nf : Renamer\n⊢ update a x ∘ f.lift = update (a ∘ f) x']</proofstate>
  --brief <proofstate>['α : Type u\na : Assignment α\nx : α\nf : Renamer\n⊢ update a x ∘ f.lift = update (a ∘ f) x']</proofstate>
  funext j; cases j with <proofstate>['case h\nα : Type u\na : Assignment α\nx : α\nf : Renamer\nj : Var\n⊢ (update a x ∘ f.lift) j = update (a ∘ f) x j']</proofstate>
  | zero => simp [update, Renamer.lift]
  | succ n => simp [Function.comp, update, Renamer.lift]
  --unbrief

theorem satisfies_rename : satisfies M a (φ.rename f) ↔
                           satisfies M (a ∘ f) φ := by <proofstate>['α : Type u\nS : Signature\nM : Model S α\nφ : Formula S\na : Assignment α\nf : Renamer\n⊢ satisfies M a (φ.rename f) ↔ satisfies M (a ∘ f) φ']</proofstate>
  --brief <proofstate>['α : Type u\nS : Signature\nM : Model S α\nφ : Formula S\na : Assignment α\nf : Renamer\n⊢ satisfies M a (φ.rename f) ↔ satisfies M (a ∘ f) φ']</proofstate>
  induction φ generalizing a f with <proofstate>['α : Type u\nS : Signature\nM : Model S α\nφ : Formula S\na : Assignment α\nf : Renamer\n⊢ satisfies M a (φ.rename f) ↔ satisfies M (a ∘ f) φ']</proofstate>
  | bot => simp [satisfies, Formula.rename]
  | rel r t => simp [satisfies, Function.comp_assoc, Formula.rename]
  | imp g h ihg ihh => simp [satisfies, ihg, ihh, Formula.rename]
  | all g ih => <proofstate>['case all\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\n⊢ satisfies M a (g.all.rename f) ↔ satisfies M (a ∘ f) g.all']</proofstate>
    simp only [satisfies, Formula.rename] <proofstate>['case all\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\n⊢ (∀ (x : α), satisfies M (update a x) (g.rename f.lift)) ↔ ∀ (x : α), satisfies M (update (a ∘ f) x) g']</proofstate>
    constructor <proofstate>['case all.mp\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\n⊢ (∀ (x : α), satisfies M (update a x) (g.rename f.lift)) → ∀ (x : α), satisfies M (update (a ∘ f) x) g', 'case all.mpr\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\n⊢ (∀ (x : α), satisfies M (update (a ∘ f) x) g) → ∀ (x : α), satisfies M (update a x) (g.rename f.lift)']</proofstate>
    · intro h x <proofstate>['case all.mp\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\nh : ∀ (x : α), satisfies M (update a x) (g.rename f.lift)\nx : α\n⊢ satisfies M (update (a ∘ f) x) g']</proofstate>
      have := (@ih (update a x) f.lift).mp (h x); <proofstate>['case all.mp\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\nh : ∀ (x : α), satisfies M (update a x) (g.rename f.lift)\nx : α\nthis : satisfies M (update a x ∘ f.lift) g\n⊢ satisfies M (update (a ∘ f) x) g']</proofstate>
      rwa [update_comp_lift] at this
    · intro h x <proofstate>['case all.mpr\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\nh : ∀ (x : α), satisfies M (update (a ∘ f) x) g\nx : α\n⊢ satisfies M (update a x) (g.rename f.lift)']</proofstate>
      apply (@ih (update a x) f.lift).mpr <proofstate>['case all.mpr\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\nh : ∀ (x : α), satisfies M (update (a ∘ f) x) g\nx : α\n⊢ satisfies M (update a x ∘ f.lift) g']</proofstate>
      rw [update_comp_lift] <proofstate>['case all.mpr\nα : Type u\nS : Signature\nM : Model S α\ng : Formula S\nih : ∀ {a : Assignment α} {f : Renamer}, satisfies M a (g.rename f) ↔ satisfies M (a ∘ f) g\na : Assignment α\nf : Renamer\nh : ∀ (x : α), satisfies M (update (a ∘ f) x) g\nx : α\n⊢ satisfies M (update (a ∘ f) x) g']</proofstate>
      exact h x
  --unbrief

theorem inst_assign_comp : a ∘ Var.inst_at t level =
                           inst_assign a t level := by <proofstate>['α : Type u\na : Assignment α\nt : Var\nlevel : Level\n⊢ a ∘ t.inst_at level = inst_assign a t level']</proofstate>
  --brief <proofstate>['α : Type u\na : Assignment α\nt : Var\nlevel : Level\n⊢ a ∘ t.inst_at level = inst_assign a t level']</proofstate>
  funext j; simp only [Function.comp, Var.inst_at, inst_assign]; split_ifs <;> rfl
  --unbrief

theorem satisfies_inst_at : satisfies M a (φ.inst_at t level) ↔
                            satisfies M (inst_assign a t level) φ := by <proofstate>['α : Type u\nS : Signature\nM : Model S α\nφ : Formula S\na : Assignment α\nt : Var\nlevel : Level\n⊢ satisfies M a (Formula.inst_at t level φ) ↔ satisfies M (inst_assign a t level) φ']</proofstate>
  --brief <proofstate>['α : Type u\nS : Signature\nM : Model S α\nφ : Formula S\na : Assignment α\nt : Var\nlevel : Level\n⊢ satisfies M a (Formula.inst_at t level φ) ↔ satisfies M (inst_assign a t level) φ']</proofstate>
  rw [Formula.inst_at_eq_rename, satisfies_rename, inst_assign_comp]
  --unbrief
```

Soundness
===
Soundness means that everything provable is also true: `Γ ⊢ φ → Γ ⊨ φ`.

We prove soundness for each possible way the proof `Γ ⊢ φ` might end.

```lean
theorem sound_ax (h : φ ∈ Γ) : Γ ⊨ φ := by <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nh : φ ∈ Γ\n⊢ Γ ⊨ φ']</proofstate>
  intro α M a hψ <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nh : φ ∈ Γ\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\n⊢ satisfies M a φ']</proofstate>
  exact hψ φ h

theorem sound_bot_elim (h : Γ ⊨ Formula.bot) : Γ ⊨ φ := by <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nh : Γ ⊨ Formula.bot\n⊢ Γ ⊨ φ']</proofstate>
  intro α M a hΓ <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nh : Γ ⊨ Formula.bot\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\n⊢ satisfies M a φ']</proofstate>
  exact absurd (h M a hΓ) (by simp [satisfies])

theorem sound_im_intro (h : Γ ∪ {φ} ⊨ ψ) : Γ ⊨ Formula.imp φ ψ := by <proofstate>['S : Signature\nΓ : Context S\nφ ψ : Formula S\nh : Γ ∪ {φ} ⊨ ψ\n⊢ Γ ⊨ φ.imp ψ']</proofstate>
  intro α M a hΓ hφ <proofstate>['S : Signature\nΓ : Context S\nφ ψ : Formula S\nh : Γ ∪ {φ} ⊨ ψ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nhφ : satisfies M a φ\n⊢ satisfies M a ψ']</proofstate>
  exact h M a (fun ω hω => by <proofstate>['S : Signature\nΓ : Context S\nφ ψ : Formula S\nh : Γ ∪ {φ} ⊨ ψ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nhφ : satisfies M a φ\nω : Formula S\nhω : ω ∈ Γ ∪ {φ}\n⊢ satisfies M a ω']</proofstate>
    cases hω with <proofstate>['S : Signature\nΓ : Context S\nφ ψ : Formula S\nh : Γ ∪ {φ} ⊨ ψ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nhφ : satisfies M a φ\nω : Formula S\nhω : ω ∈ Γ ∪ {φ}\n⊢ satisfies M a ω']</proofstate>
    | inl h1 => exact hΓ ω h1
    | inr h1 => simp at h1; rw [h1]; exact hφ)
```

Soundness Continued
===

```lean
theorem sound_im_elim (h₁ : Γ ⊨ Formula.imp φ ψ) (h₂ : Γ ⊨ φ) : Γ ⊨ ψ := by <proofstate>['S : Signature\nΓ : Context S\nφ ψ : Formula S\nh₁ : Γ ⊨ φ.imp ψ\nh₂ : Γ ⊨ φ\n⊢ Γ ⊨ ψ']</proofstate>
  intro α M a hΓ <proofstate>['S : Signature\nΓ : Context S\nφ ψ : Formula S\nh₁ : Γ ⊨ φ.imp ψ\nh₂ : Γ ⊨ φ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\n⊢ satisfies M a ψ']</proofstate>
  exact h₁ M a hΓ (h₂ M a hΓ)

theorem sound_all_intro (h : Formula.shift '' Γ ⊨ φ) : Γ ⊨ Formula.all φ := by <proofstate>["S : Signature\nΓ : Context S\nφ : Formula S\nh : Formula.shift '' Γ ⊨ φ\n⊢ Γ ⊨ φ.all"]</proofstate>
  intro α M a hΓ x <proofstate>["S : Signature\nΓ : Context S\nφ : Formula S\nh : Formula.shift '' Γ ⊨ φ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nx : α\n⊢ satisfies M (update a x) φ"]</proofstate>
  exact h M (update a x) (fun χ hχ => by <proofstate>["S : Signature\nΓ : Context S\nφ : Formula S\nh : Formula.shift '' Γ ⊨ φ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nx : α\nχ : Formula S\nhχ : χ ∈ Formula.shift '' Γ\n⊢ satisfies M (update a x) χ"]</proofstate>
    obtain ⟨ψ, hψ, rfl⟩ := hχ <proofstate>["S : Signature\nΓ : Context S\nφ : Formula S\nh : Formula.shift '' Γ ⊨ φ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nx : α\nψ : Formula S\nhψ : ψ ∈ Γ\n⊢ satisfies M (update a x) ψ.shift"]</proofstate>
    rw [show ψ.shift = ψ.rename (Var.shift 0) from rfl, satisfies_rename] <proofstate>["S : Signature\nΓ : Context S\nφ : Formula S\nh : Formula.shift '' Γ ⊨ φ\nα : Type\nM : Model S α\na : Assignment α\nhΓ : ∀ ψ ∈ Γ, satisfies M a ψ\nx : α\nψ : Formula S\nhψ : ψ ∈ Γ\n⊢ satisfies M (update a x ∘ Var.shift 0) ψ"]</proofstate>
    exact hΓ ψ hψ)
```

Soundess Continued
===

```lean
theorem sound_all_elim (h : Γ ⊨ Formula.all φ) : Γ ⊨ φ.inst t := by <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nt : Var\nh : Γ ⊨ φ.all\n⊢ Γ ⊨ Formula.inst t φ']</proofstate>
  intro α M a hψ <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nt : Var\nh : Γ ⊨ φ.all\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\n⊢ satisfies M a (Formula.inst t φ)']</proofstate>
  rw [Formula.inst_eq, satisfies_inst_at] <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nt : Var\nh : Γ ⊨ φ.all\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\n⊢ satisfies M (inst_assign a t 0) φ']</proofstate>
  have : inst_assign a t 0 = update a (a t) := <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nt : Var\nh : Γ ⊨ φ.all\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\nthis : inst_assign a t 0 = update a (a t)\n⊢ satisfies M (inst_assign a t 0) φ']</proofstate>
    funext fun j => by simp [inst_assign, update]
  rw [this] <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nt : Var\nh : Γ ⊨ φ.all\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\nthis : inst_assign a t 0 = update a (a t)\n⊢ satisfies M (update a (a t)) φ']</proofstate>
  exact h M a hψ (a t)

theorem sound_em : Γ ⊨ Formula.or (Formula.not φ) φ:= by <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\n⊢ Γ ⊨ φ.not.or φ']</proofstate>
  intro  α M a hψ h1 <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\nh1 : satisfies M a φ.not.not\n⊢ satisfies M a φ']</proofstate>
  unfold Formula.not at h1 <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\nh1 : satisfies M a ((φ.imp Formula.bot).imp Formula.bot)\n⊢ satisfies M a φ']</proofstate>
  simp[satisfies] at h1 <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nα : Type\nM : Model S α\na : Assignment α\nhψ : ∀ ψ ∈ Γ, satisfies M a ψ\nh1 : satisfies M a φ\n⊢ satisfies M a φ']</proofstate>
  exact h1
```

Soundess Finished
===
And now the main result:

```lean
open Provable Formula in
theorem sound : Γ ⊢ φ → Γ ⊨ φ := by <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\n⊢ Γ ⊢ φ → Γ ⊨ φ']</proofstate>
  intro h <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nh : Γ ⊢ φ\n⊢ Γ ⊨ φ']</proofstate>
  induction h with <proofstate>['S : Signature\nΓ : Context S\nφ : Formula S\nh : Γ ⊢ φ\n⊢ Γ ⊨ φ']</proofstate>
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

This theorem is more complex than soundness and at this point I have it only partially finished.



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


Future Work
===

Spring 2026: Weekly research meetings on formalizing logic.


```lean
--hide
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

