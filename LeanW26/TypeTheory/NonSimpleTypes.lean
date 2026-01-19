--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26.NonSimpleTypes

/-
Beyond Simple Types
===

The Lambda Cube
===

Is there a non-simply typed λ-calculus? Yes!

- **Simple types** (λ→)Terms depend on terms.
- **Polymorphism** (λ2) Functions can depend on types.
- **Parameterized types** (λ<u>ω</u>) Types can depend on types.
- **Dependent types** (λP) Types can depend on terms.

Putting all of these together you get the **CoC** the **Calculus of Constructions** (λC),
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

**Polymorphism** in Lean is handled with the `Π` type formation operator, which
quantifies over types, like `λ` quantifies over terms.

For example,
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

A **parameterized** type has a constructor taking another type as a parameter.

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


/- The notation [Add α] ensures that α is a type that has addition (See Type classes)-/

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
Non-recursive Inductive Types
===

When a type isn't recursive, as in:

-/

inductive ThreeVal where | one | two | three

/-
The `.casesOn` instance is particularly simple.
-/

#check ThreeVal.casesOn
  -- {motive : ThreeVal → Sort u} → ∀ t : ThreeVal,
  -- motive ThreeVal.one → motive ThreeVal.two →
  -- motive ThreeVal.three → motive t

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
```lean
inductive T where | mk : (T → Nat) → T
> arg #1 of 'T.mk' has a non positive occurrence of the datatypes being declared
```
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

**Lean:** "Any argument to the constructor in which [the typed being
defined] occurs is a dependent arrow type in which the inductive
type under definition occurs only as the resulting type, where the
indices are given in terms of constants and previous arguments." (TPIL)

If you see the "positivity" error, try to understand
how you could accidentally write a non-terminating function with your type. Then refactor.

Note: Lean added coinductive Prop definitions in v4.25.
We will cover these when we get to proofs.

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
-/


/-
Type Classes
===
A **type class** is a way to associate data and methods with all
type definitions that meet the class's specifications.

For example, Lean's Standard Library defines
-/

--hide
namespace Temp
--unhide

class Zero (α : Type) where
  zero : α

class Add (α : Type) where
  add : α → α → α

/- Which can be used in functions, as in the following, which
allows you to sum a list of anything that has a `zero` and an `add` function. -/

def sum {α : Type} (f : ℕ → α) (n : ℕ) [hz : Zero α] [ha : Add α] :=
  match n with
  | .zero => hz.zero
  | .succ k => ha.add (f n) (sum f k)





/-
Instances
===
You can instantiate a type class for a given type using the `instance` keyword.
-/

instance : Zero String where
  zero := ""

instance : Add String where
  add a b := b ++ a

#eval sum (fun n => String.singleton (Char.ofNat (n+96))) 26
      -- "abcdefghijklmnopqrstuvwxyz"

/- or -/

instance : Zero Nat where
  zero := .zero

instance : Add Nat where
  add := .add

#eval sum (fun n => n^2) 26    -- 6201

--hide
end Temp
--unhide


/-
Lean/Mathlib Classes
===

There are a **huge** number of type classes in Lean and we will encounter many
of them.


<img src="img/mathlib-hierarchies.jpg" width=85%></img>

We'll go into some of these in a latter class.

Naturals Revisited
===

For example, suppose we defined our own version of the natural numbers with: -/

mutual
  inductive Ev
  | zero : Ev
  | succ : Od → Ev
  deriving Repr              -- allows Lean to print Ev terms

  inductive Od
  | succ : Ev → Od
  deriving Repr              -- allows Lean to print Od terms
end

def Naturals := Ev ⊕ Od

def Naturals.zero : Naturals := .inl Ev.zero

def Naturals.succ (x : Naturals) : Naturals := match x with
  | .inl a => .inr (Od.succ a)
  | .inr a => .inl (Ev.succ a)

/-
Using Lean's Natural Number Syntax
===

Writing `(succ (succ zero))` for two gets old fast. We would like to
be able to write
-/

#check_failure (0:Naturals)
#check_failure (1:Naturals)
#check_failure (2:Naturals)

/- Lean has classes for zero and one. -/

instance : Zero Naturals := ⟨ .zero ⟩
instance : One Naturals := ⟨ .succ .zero ⟩

#check (0:Naturals)
#check (1:Naturals)

/- We can also convert Lean's `Nat` to our `Naturals` (obviating the
need for `Naturals`, but whatever).-/

def of_nat (n : Nat) : Naturals := match n with
  | Nat.zero => .zero
  | Nat.succ k => .succ (of_nat k)

instance {n : Nat} : OfNat Naturals n := ⟨ of_nat n ⟩

#check (2:Naturals)

/-
Defining Addition
===

First we define addition for `Ev` and `Od`
-/
mutual
  def add_ev_ev (x y : Ev) := match x with
    | .zero => y
    | .succ k => .succ (add_od_ev k y)
  def add_od_ev (x : Od) (y : Ev) := match x with
    | .succ k => .succ (add_ev_ev k y)
  def add_ev_od (x : Ev) (y : Od) := match x with
    | .zero => y
    | .succ k => .succ (add_od_od k y)
  def add_od_od (x y : Od) := match x with
    | .succ k => .succ (add_ev_od k y)
end

/- Then we define addition for `Naturals`. -/

def Naturals.add (x y : Naturals) : Naturals := match x,y with
  | .inl a, .inl b => .inl (add_ev_ev a b)
  | .inl a, .inr b => .inr (add_ev_od a b)
  | .inr a, .inl b => .inr (add_od_ev a b)
  | .inr a, .inr b => .inl (add_od_od a b)

/-
Instantiating Addition
===

Now we can define and instantiate addition.
-/

instance : HAdd Naturals Naturals Naturals := ⟨ Naturals.add ⟩
instance : Add Naturals := ⟨ Naturals.add ⟩

def f (x y : Naturals) := x + y + 1

#eval f 2 3         -- 5

/- Other classes we might define for our `Naturals` type include -/

#check (Add, Sub, Mul, Mod, Div, LT, LE)
#check (HAdd, HSub, HMul, HDiv)
#check Inhabited
#check Ord
#check LinearOrder
#check Coe
#check CommSemiring      -- adds theorems that interact with simplifier
#check Countable         -- adds theorems

/-
Exercises
===

<ex /> Recall the definition of `Dyadic` from Slide Deck II.4.
- Instantiate `Zero` and `One`
- To compute a function `f : α → α` `n` times, you can use the f^[n] notation.
Check that the following notation works for your `Dyadic`
```lean
#eval add_one^[8] 0    - 8
#eval double^[8] 1     - 256
#eval half^[8] 1       - 1/256
```
<ex /> Sums of Dyadics
- Instantiate `HAdd` and `Add` for `Dyadic`.
- Use the `sum` function with `Dyadic` to compute $\sum_{n=1}^8 n\cdot2^{-n}$ and use
your `.to_rat` function to check the answer.

<ex /> Products of Dyadics
- Instantiate `HMul` and `Mul` for `Dyadic`.
- Define `product` similarly to how we defined `sum`. Compute
$\prod_{n=1}^8 n\cdot2^{-n}$ with `Dyadic` and use your `.to_rat` function to check the answer.

-/

/-
References
===

- Thierry Coquand and Gérard Huet, The Calculus of Constructions, *Information and Computation*,
Vol. 76, Issue 2, pp. 95–120, 1988.
- Thierry Coquand and Christine Paulin, Inductively Defined Types, in COLOG-88: International
Conference on Computer Logic, *Lecture Notes in Computer Science*, vol. 417, Springer, 1988.
- Homotopy Type Theory: Univalent Foundations of Mathematics
The Univalent Foundations Program Institute for Advanced Study (https://homotopytypetheory.org/book/).


-/

--hide
end LeanW26.NonSimpleTypes
--unhide
