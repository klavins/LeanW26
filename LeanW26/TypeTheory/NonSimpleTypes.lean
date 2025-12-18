import Mathlib

namespace LeanW26.NonSimpleTypes

/-
Beyond Simple Types
===

Is there a non-simply typed λ-calculus? Yes!

- **Simple types** (λ→)Terms depend on terms.
- **Polymorphism** (λ2) Functions can depend on types.
- **Parameterized types** (λ<u>ω</u>) Types can depend on types.
- **Dependent types** (λP) Types can depend on terms.

Putting all of these together you get the **CoC** the **Caclulus of Constructions** (λC),
part of a well-studied framework called the *Lambda Cube*.

<img src="https://upload.wikimedia.org/wikipedia/commons/thumb/c/cd/Lambda_Cube_img.svg/2560px-Lambda_Cube_img.svg.png" width=30%></img>


Adding Inductive Types
===

If we add

- **Inductive Types**: Types are defined with constructors and recursion.

We get **CIC**, the **Calculus of Inductive Constructions**.

Coq, Rocq, and Lean are all loose implementations of CIC.

Lean adds
- Quotients
- Typeclasses
- Universe polymorphism
- Meta programming

Agda is similar, but based on Martin-Löf type theory (MLTT).

Review: Simple Types
===

As described in the previous slide deck, **simple types** consist of `Prop`, `Type u`
and arrow types from `α → β` where `α` and `β` are types.

Terms with these types are
- **Variables** `x : α` where `x` is a symbol and `a` is a type.
- **Abstractions** `fun (x : α) => M x` where
    - `x` is a `bound` variable
    - `α` is a type
    - `M x : β` is a term (usually containing `x`)
- **Applications** `x y : β` where `x : α → β` and `y : α`


Polymorphism
===

**Polymorphism** in Lean is handled the `Π` type formation operator, which
quantifies over types, like `λ` quantifies over terms. For example,
-/

universe u

def id1 : Π (α : Type u), α → α := fun _ x => x
def id2 : Π {α : Type u}, α → α := fun x => x
def id3 {α : Type u} := fun (x : α) => x
def id4 : (α : Type u) → α → α := fun (_ : Type u) => fun x => x
def id5 : ∀ α, α → α := fun _ => fun x => x

/-
Notes:
- `Π` and `∀` are defined as syntactic sugar for `forall`
- `Π` requires Mathlib.
- Regular function types are a special case of Π types.
- The above functions are also **universe polymorphic**
-/

/-
Parameterized types
===

A **parameterized** type has a constructor taking another type as a paramter.

The standard example is List.
-/

inductive MyList {α : Type} where
  | nil : MyList
  | cons : α → MyList → MyList

/-
Note that the constructor for MyList is polymorphic, as one would expect:
-/

#check MyList.cons    -- {α : Type} → α → MyList → MyList


/-
Dependent types
===

A **dependent** type depends on a term. A vector of a given length
is an example. -/

inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons {n} :  α → Vec α n → Vec α (n + 1)

/-
Here is a polymorphic function that adds two vectors together.
-/

def Vec.add {α : Type u} [Add α] {n : Nat} (x y : Vec α n)
  : Vec α n :=
  match x, y with
  | nil, nil => nil
  | cons a w, cons b z => cons (a+b) (Vec.add w z)


/- The notation [Add α] ensures that α is a type that has addition (See Typeclasses)-/

#check_failure Vec.add (Vec.nil.cons 1) ((Vec.nil.cons 1).cons 2)


/-
Exercises
===

<ex/> Define a parameterized structure type called `Pair` that represents a
pair of values having not necessarily the same types.

<ex/> Define a polymorphic function that swaps the order of a `Pair`. What is
it's type?

<ex/> Consider the dependent type

-/

def chooseType : Bool → Type
| true  => Nat
| false => String

/- Create a function `f : Bool → chooseType Bool`. -/



/-
Sigma Types
===

A Sigma type is
parameterized (by `α` and `β`), polymorphic (via the type of `β`),
and dependent (via the constructor for `snd`). In Lean, Sigma is defined by
```lean
structure Sigma {α : Type u} (β : α → Type v) where
  fst : α
  snd : β fst
```
For example, to carry around a length and a default vector of that
length, we could do:

-/
#check Sigma.mk 0 Vec.nil
#check Sigma.mk 1 (Vec.nil.cons 0)

/-
A Function on Sigma Types
===

Lean provides the notation `Σ` for Sigma types.
-/

def Vec.default (n : Nat) : Σ (n:Nat), Vec Nat n := match n with
  | 0 => Sigma.mk 0 Vec.nil
  | n+1 => let v := (Vec.default n)
           Sigma.mk (v.fst+1) (v.snd.cons 0)

#check Vec.default 3 --- (n : ℕ) × Vec ℕ n

/-
Exercises
===

<ex /> Define a function
```lean
forget : Σ (n:Nat), Vec Nat n → List Nat
```
that takes a Sigma value representing a length and a vector of that length
and returns the vector turned into a list.

-/

/-
Inductive Arguments
===

In the lambda calculus we encoded natural numbers using Church encodings.


What if we wanted to do a proof by induction? We would have to do that
*outside* the lambda calculus.

In particular, we cannot expression the inductive principle:

```lean
∀ (P : ℕ → Prop), P 0 → (∀ n, P n → P (n+1)) → ∀ n, P n
```

because we don't have a definition of ℕ as a type with an inductive
principle that goes with it.

Inductive Types
===

Formally, an **inductive type** is a type with

- **A Formation Rule** declaring what type universe the elements live in
- **Constructors** for making elements of the type
- **An Elimination Rule** to define functions (and proofs) using the type
- **Computation Rules** define how to reduce terms

For example,

```lean
inductive Nat : Type where         -- Formation rule
  | zero : Nat                     -- Constructor 1
  | succ : Nat → Nat               -- Constructor 2
```


The Recursor
===

Every time you define an inductive type, you get an inductive
schema as a definition:
-/

#check Nat.rec   -- {motive : Nat → Sort u} →
                 -- motive Nat.nada →
                 -- (∀ n : Nat, motive n → motive n.mas) →
                 -- ∀ t : Nat, motive t

/- You also get a way to show terms constructed differently are different. -/

#check Nat.noConfusion -- {P : Sort u} →
                      -- {x1 x2 : ℕ} →
                      -- x1 = x2 →
                      -- Nat.noConfusionType P x1 x2

#check Nat.noConfusionType -- Sort u → ℕ → ℕ → Sort u

/-
We will later use `noConfusion` to prove statements like `m.succ ≠ m.succ.succ`.
-/

/-
Derived Recursors
===
Lean also defines the following in terms of `.rec`.
-/

#check Nat.recOn   -- {motive : Nat → Sort u} →
                   -- ∀ t : Nat,
                   --   motive Nat.nada →
                   --   (∀ n : Nat, motive n → motive n.mas) →
                   --   motive t

#check Nat.casesOn -- {motive : Nat → Sort u} →
                   -- ∀ t : Nat,
                   --   motive Nat.nada →
                   --   (∀ a : Nat, motive a.mas) →
                   --   motive t

/-
Nonrecursive Inductive Types
===

When a type isn't recursive, as in:

-/

inductive ThreeVal where | one | two | three

/-
The `.casesOn` instance is particularly simple.
-/

#check ThreeVal.casesOn  -- {motive : ThreeVal → Sort u} →
                         -- ∀ t : ThreeVal,
                         -- motive ThreeVal.one →
                         -- motive ThreeVal.two →
                         -- motive ThreeVal.three →
                         -- motive t

/- For example: -/

def ThreeVal.toNat (x : ThreeVal) : ℕ :=
  ThreeVal.casesOn x 1 2 3

#eval ThreeVal.one.toNat     -- 1

/-
Recursors With Recursive Definitions
===

The following are equivalent
-/

def even1 (n : Nat) : Bool :=
  Nat.recOn n true (fun k pk => ¬pk)

def even2 (n : Nat) : Bool := match n with
  | .zero => true
  | .succ k => ¬ even2 k


/-
Restrictions on Inductive Types
===

Consider:
```lean
inductive T where
| mk : (T → Nat) → T
```
> (kernel) arg #1 of 'T.mk' has a non positive
> occurrence of the datatypes being declared

Lean determines that defining a function of type `T → Nat` would be
self referential.
```lean
def loop (b : T) : Nat := match b with
  | T.mk f => f b
```
which unrolls to
```lean
def loop (b : T) : Nat := match b with
  | T.mk f => match b with
    | T.mk f => f b --- etc.
```
An infinite loop.
-/




/-
Positivity in Inductive Types
===

**Lean:** "Any argument to the constructor in which [the typed being defined]
occurs is a dependent arrow type in which the inductive type under definition
occurs only as the resulting type, where the indices are given in terms of
constants and previous arguments." (https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/)

**Agda:** Somewhat stronger requirement. The defined type "may only occur strictly positively in the types of their arguments."(https://agda.readthedocs.io/en/latest/language/data-types.html)

**Roq:** Uses the CoInductive keyword.

**Haskell**: Perfectly happy with nonterminating things.

-/


/-
Exercise
===

<ex /> Use List.rec to define a function that computes the
length of a list. Use only List.rec, Nat.zero and Nat.succ.

Start with
```lean
def length {α} (L : List α) : Nat :=
  List.rec sorry sorry sorry sorry
```
-/






/-
Coming Soon: Using the Recursor in Proofs
===

You can use the recursor in proofs (we'll get to this later).
-/

#check Nat.noConfusion

open Nat in
example : ∀ (n : Nat), n.succ ≠ zero :=
  Nat.rec (Nat.noConfusion) (fun n hn => Nat.noConfusion)

/- Which fortunately can also be written: -/
example : ∀ (n : Nat), n.succ ≠ .zero := by
  intro n
  induction n with
  | zero => exact Nat.noConfusion
  | succ k ih => exact Nat.noConfusion


/-
Type Classes
===
A **type class** is a way to associate data and methods with all
type definitions that meet the class's specifications.

For example,
-/

class HasZero (α : Type) where
  zero : α

class HasAdd (α : Type) where
  add : α → α → α

/- Which can then be used in functions, as in the following, which
allows you to sum a list of anything that has a `zero` and an `add` funciton. -/

def sum {α : Type} (f : ℕ → α) (n : ℕ) [hz : HasZero α] [ha : HasAdd α] :=
  match n with
  | .zero => hz.zero
  | .succ k => ha.add (f n) (sum f k)

/-
Instances
===
You can instantiate a type class for a given type using the `instance` keyword.
-/

instance : HasZero String where
  zero := ""

instance : HasAdd String where
  add a b := b ++ a

#eval sum (fun n => String.singleton (Char.ofNat (n+96))) 26

/- or -/

instance : HasZero Nat where
  zero := .zero

instance : HasAdd Nat where
  add := .add

#eval sum (fun n => n^2) 26


/-
Lean/Mathlib Classes
===

There are a **huge** number of type classes in Lean and we will encounter many
of them. For example: -/

inductive Numero where
  | nada : Numero
  | mas : Numero → Numero

def Numero.add (x y : Numero) := match x with
  | nada => y
  | mas z => mas (add z y)

instance : One Numero := ⟨ .mas .nada ⟩
instance : HAdd Numero Numero Numero := ⟨ Numero.add ⟩

def f (x y : Numero) := x + y + 1

/-
Later we will build algebraic structures for our datatypes. For example,
```
instance : Group ℤ := ...
```
-/

/-
Various Advanced Types (Not in Lean)
===

**Univalence**: In mathematics, we often reason about objects *up to isomorphism*.
The *univalence axiom* says `A ≃ B → A = B`, meaning once you prove an isomorphism,
you get equality. In Lean, you do this in a clunk way with quotients.

**Higher Inductive Types**: Point constructors and path constructors.

**HOTT**: Types are spaces, equalities are paths between
equal objects. Equalities of equalities are higher order paths.
 Univalence + Inductive types with a homotopy interpretation of
types as spaces, terms as points, and equalities as maths.
Very elegant math, but decidability issues abound.

**Cubical Types**: Introduces an interval object `I = [0,1]` and cubes made from it.
Path types are `I → Type`. Makes (requires) HITs to be constructive. Makes
type checking decidable.

**Many Others**: Observational type theory, modal type theory, linear type theory, ...



References
===

- Thierry Coquand and Gérard Huet, The Calculus of Constructions, *Information and Computation*,
Vol. 76, Issue 2, pp. 95–120, 1988.
- Thierry Coquand and Christine Paulin, Inductively Defined Types, in COLOG-88: International
Conference on Computer Logic, *Lecture Notes in Computer Science*, vol. 417, Springer, 1988.
- Homotopy Type Theory: Univalent Foundations of Mathematics
The Univalent Foundations Program Institute for Advanced Study (https://homotopytypetheory.org/book/).


-/


/-
Exercises
===

<ex /> Using the `Vec` class we made, define function that does scalar multiplication
of a scalar and a vector to produce another vector. Test with examples.

<ex /> Instantiate `HasZero` and `HasAdd` for `Vec` and show an example where the `sum`
function we wrote works on vectors. Also show that you can sum a function of
vectors of `Numero` values.

<ex /> Define multiplication for `Numero`, instantiate `HMul` and `Mul` classes,
and define a function for the sum of squares of two `Numero` values. Test with examples.

<ex /> Write a function that converts a `Nat` into a `Numero`. Instantiate the class
`OfNat` with `Numero` so that the following function type checks:
```lean
def g (x : Numero) : Numero := x*x + 7
```

-/

--hide
end LeanW26.NonSimpleTypes
--unhide
