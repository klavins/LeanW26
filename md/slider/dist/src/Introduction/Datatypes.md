
Datatypes
===


Introduction to Inductively Defined Types
===


All the types we've been looking at
```lean
ℕ, ℚ, ℝ, List,  ...
```
are *inductively defined*. That means, they are defined by

   - Some number of base cases
   - Some number of recursive constructors

We'll have more to say about the theory of inductive types later.
For now we'll describe them via examples.


Natural Numbers
===


```lean
inductive MyNat where
  | zero : MyNat               -- base case
  | succ : MyNat → MyNat         -- recursive constructor

#check MyNat                   -- Type

open MyNat

#check zero                  -- all Nat
#check succ zero             -- 1
#check succ (succ zero)      -- 2
#check zero.succ
#check zero.succ.succ
```

This is how you build the natural numbers in Lean. The numerals 0, 1, 2, etc.
are just "syntactic sugar".
 
```lean
#eval Nat.zero == 0
#eval Nat.zero.succ.succ.succ == 3
```
!
Complex Numbers
===

Many types are inductive. For example, here is a complex number:

```lean
inductive MyComplex where
  | mk : Real → Real → MyComplex

def MyComplex.re (x : MyComplex) : Real :=
  match x with
  | mk a _ => a

def MyComplex.im (x : MyComplex) : Real :=
  match x with
  | mk _ b => b

#check MyComplex.mk 1 2

noncomputable
def MyComplex.abs (x : MyComplex) : Real := Real.sqrt (x.re^2 + x.im^2)
```

Three Valued Logic
===

Not all inductive types have recursive constructors. `Bool` has only bases cases.
Here's a similar example:

```lean
inductive TriBool where
  | T : TriBool
  | F : TriBool
  | U : TriBool

open TriBool

def and (A B : TriBool) :=
  match A, B with
  | T, x   => x
  | F, _   => F
  | U, F   => F
  | U, _   => U

#eval and T (and U F)   -- f
```

Exercises
===

<ex/> Define an alternative complex number in terms of its magnitude and argument.
Note that the type of non-negative reals is defined as `NNReal`.

<ex/> Define `or` for `TriBool`.



Binary Trees
===

Here is a an extended example where we define a polymorphic Binary Tree type and
show how to start a library of functions for it. 
```lean
inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : A → BTree A → BTree A → BTree A
```
 Once a new type is defined, we usually put all of its functions in a *namespace*.
The following line opens that namespace. 
```lean
open BTree             -- Variables are now all BTree.*

#check leaf            -- Temp.BTree.leaf {A : Type} : A → BTree A
#check node            -- Temp.BTree.node {A : Type} : A → BTree A
                       -- → BTree A → BTree A
```

Defining a Binary Tree
===

Here's an example tree.

```lean
def my_tree := node 1 (leaf 2) (node 3 (leaf 4) (leaf 5))
```

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQeSlUTnaC2yPFo8vJgGKOCTcHxq63r2fP37AMPvyMGzSi53ZkclclgY51zSN4D3sCczjretVs3HIQW/pub?w=960&amp;h=720" width=30%>



Defining Functions on Inductive Types
===

Here's an example function to convert tree to a list.
It can be referred to as `BTree.to_list` when `BTree` is not open. 
```lean
def to_list {A : Type} (T : BTree A) : List A :=
  match T with
  | leaf a => [a]
  | node a left right => [a] ++ (to_list left) ++ (to_list right)

#eval to_list my_tree   -- [1,2,3,4,5]
```

Representing Values
===

When we define a tree and evaluate it, we get a cumbersome representation:  
```lean
#eval my_tree -- BTree.node 1 (BTree.leaf 2)
              -- (BTree.node 3 (BTree.leaf 4) (BTree.leaf 5))
```
 We can tell Lean to make a more compact representation. 
```lean
def to_str {A : Type} [sa : ToString A] (T : BTree A) : String :=
  match T with
  | leaf a => toString a
  | node a L R =>  "(" ++ (toString a) ++ " " ++ (to_str L) ++ " " ++ (to_str R) ++ ")"

instance {A : Type} [Repr A] [ToString A] : Repr (BTree A) := {
  reprPrec := fun T _ => to_str T
}
```

Now when we evaluate we get: 
```lean
#eval my_tree             -- (1 2 (3 4 5))
```

Mapping to Trees
===

Here is an example function. Note the use of curly braces since `A` and
`B` are inferable from the argument `f`.


```lean
def bt_map {A B : Type} (f : A → B) (T : BTree A) : BTree B :=
  match T with
  | leaf a => leaf (f a)
  | node a left right => node (f a) (bt_map f left) (bt_map f right)

#eval bt_map (fun x => x*x) (node 0 my_tree my_tree)
```

Exercises
===

<ex/> Define a function `swap` that takes a `BTree` and swaps the order of the
children in all nodes. You should get, for example:

```lean
#eval swap my_tree             -- (1 (3 5 4) 2)
```


Mutually Inductive Types
===

Sometimes you want to define two types inductively where the definition of
one depends on the definition of the other. For example:

```lean
mutual
  inductive Ev
  | zero : Ev
  | succ : Od → Ev

  inductive Od
  | succ : Ev → Od
end

#check Ev.succ (Od.succ Ev.zero)
```

Expression Trees
===
A common use case for mutual induction is to define terms and expressions.

```lean
mutual
  inductive Term
  | var : String → Term
  | num : ℕ → Term
  | paren : Expr → Term

  inductive Expr
  | neg : Term → Expr
  | add : Term → Term → Expr
  | mul : Term → Term → Expr
end
```

Here's how you would encode 2*(x+1)

```lean
open Expr Term in
def expr : Expr := mul (num 2) (paren (add (var "x") (num 1)))
```

Exercises
===

<ex /> Write a function `Expr.CountAdds` that takes an `Expr` and returns the number of
additions in it. You will need an auxiliary function and you will have to put both
definitions in a mutual block, since they call each other.


```lean
mutual
  def Term.CountAdds (t : Term) : ℕ := sorry
  def Expr.CountAdds (e : Expr) : ℕ := sorry
end
```

Structures
===

Recall the pattern for `MyComplex` in which we

- defined an inductive type with a constructor of the form `A → A → A`
- defined accessors with `match x with | mk x y = x`.

That is so common that Lean has a convenience notation:
If you have an inductive type with *one* constructor, then you can use a *structure*.


```lean
structure Komplex where
  re : Real
  im : Real

open Komplex

def conj (x : Komplex) : Komplex:= {
  re := x.re,
  im := -x.im
}
```

Type Hints are Often Required
===

Q: Why do you think this doesn't work

```lean
def conj (x : Komplex) := {
  re := x.re,
  im := -x.im
}
```


Bracket Notation
===

You can use the `⟨ a, b ⟩` if the type is known. For example


```lean
def add (x y : Komplex) : Komplex :=
  ⟨ x.re + y.re, x.im + y.im ⟩

def negate (x : Komplex) : Komplex := ⟨ -x.re, -x.im ⟩
```

Match with Structures
===

You can use structures as though they were inductive types (since they are). 
```lean
def negate1 (x : Komplex) : Komplex :=
  match x with | mk a b => ⟨ -a, -b ⟩

def negate2 (x : Komplex) : Komplex :=
  match x with | ⟨ a, b ⟩ => ⟨ -a, -b ⟩

def negate3 (x : Komplex) : Komplex :=
  let ⟨ a, b ⟩ := x
  ⟨ -a, -b ⟩

def negate4 (x : Komplex) : Komplex := ⟨ -x.1, -x.2 ⟩
```

Exercises
===

<ex/> Define a structure `3DVector`.

<ex/> Define a cross product function of two `3DVectors` and test it on examples.



Products
===

Products represent a pair of objects.


```lean
structure MyProd (A B : Type) where
  fst : A
  snd : B

def p : MyProd Rat String := ⟨ 0, "zero" ⟩

#eval p.fst
#eval p.snd
```
 Lean's Prod uses `×`: 
```lean
def q : Rat × String := ⟨ 1, "one" ⟩
```

Using Products
===
We could have defined

```lean
def Komplex' := ℝ × ℝ
def Komplex'.re (x : Komplex') := x.fst
```

and so on. Or


```lean
def Point {α : Type} := α × α
def Vector3D' := ℝ × ℝ × ℝ
```
 The benefit is that you get a bunch of defined functions for products. The downsides are
- the defined type may not really be a cross product space
(e.g. cross products don't really have inverses).
- you have to define a lot of synonyms (e.g. `x.re = x.fst`) anyway.



Π-Types
===

A Π-Type is a generalization of a product. In type theory it is a core object not defined
in terms of some other notion.

An example of a _non-dependent_ `Pi-Type` is the set of infinite sequences of rationals.

```lean
def Qn := Π _n : ℕ, ℚ
```

This is definitionally equal to 
```lean
def Qn' := (ℕ → ℚ)
```
 An example is 
```lean
def harmonic_sequence : Qn := fun n => 1/(n+1)
```

Dependent Π-Types
===

To build an example of a _dependent_ Π-type, we first need a _dependent type_,
which is a type that depends on a parameter. For example, `Fin n` is the set of
natural numbers less than `n` (defined in the `Prelude` as a structure).

From `Fin n` we can construct

```lean
def DPT := Π n : ℕ, Fin (n+1)
```
 or equivalently 
```lean
def DPT' := (n : ℕ) → Fin (n+1)
```

which is the set of sequences `σ` of natural numbers where `σ(n) < n`. For example,

```lean
def σ1 : DPT := fun n => ⟨ n, by lia ⟩
def σ2 : DPT' := fun n => ⟨ n/2, by lia ⟩
```
 Since we haven't covered proofs yet, we'll dig in to these ideas later. 

Sums
===

A sum type represents the _choice_ of value from one of two sets.
So a value is constructed as either "in left" or "in right".


```lean
inductive MySum (A B : Type) where
  | inl : A → MySum A B
  | inr : B → MySum A B

def s1 : MySum Rat String := .inl 0
def s2 : MySum Rat String := .inr "zero"

def swap (s : MySum Rat String) : MySum String Rat :=
  match s with
  | .inl x => .inr x
  | .inr x => .inl x
```
 Lean's Sum uses `⊕`: 
```lean
def s : Rat ⊕ String := .inl 1
```

An Alternative ℕ
===

A cute use of sums is to build on our definition of Even and Odd numbers with:


```lean
def Naturals := Ev ⊕ Od
```
 Zero and successor can be defined with: 
```lean
def Naturals.zero : Naturals := .inl Ev.zero

def Naturals.succ (x : Naturals) : Naturals := match x with
  | .inl a => .inr (Od.succ a)
  | .inr a => .inl (Ev.succ a)
```

Sums as Co-products
===

A sum type is called a co-product in, for example, topology. Suppose we have
two disjoint copies of a space `X`, Then `X ⊕ X` is the type of points in
that space. They are either a point from the "left" side or a point in the "right"
side.

For example, a way to start building an identification topology might be:

```lean
def TwoR := ℝ ⊕ ℝ

def equiv (x y : TwoR) : Prop := match x,y with
  | .inl a, .inl b => a = b
  | .inr a, .inr b => a = b
  | .inl a, .inr b => a = 0 ∧ b = 0
  | .inr a, .inl b => a = 0 ∧ b = 0
```
 Then show `equiv` is an equivalence relation and take the quotient

```lean
TwoR / equiv
```
with respect to `equiv`. We'll get to how to do this later. 

Σ-Types
===

A Σ-Type represents a choice of an object from a single set. These are defined inductively.

```lean
structure Sigma {α : Type} (β : α → Type) where
  fst : α
  snd : α → β fst
```

Lean provides several equivalent notations:

```lean
def SigT   := Sigma (fun n : ℕ => Fin n)
def SigT'  := Σ n : ℕ, (Fin n)
def SigT'' := (n:ℕ) × (Fin n)
```
 As an example of a value: 
```lean
def x : SigT := ⟨ 3, 2 ⟩     -- 2 has type Fin 3
```

Exercises
===

<ex /> Rewrite your cross product function in terms of `ℝ × ℝ × ℝ`.

<ex /> You can specify a circle with a single point `r : ℝ` and a rectangle
with a pair of points `x y : ℝ`. Thus a shape might be defined as

```lean
def Shape := ℝ ⊕ (ℝ × ℝ)
```
 define functions `area (s : Shape) : ℝ` and `perimeter (s : Shape) : ℝ`.
Note that π is defined with `Real.pi` 
```lean
#check Real.pi
```

Option
===

The `Option` type is useful in situations where a value might not be available.


```lean
inductive MyOption (A : Type)
  | none : MyOption A
  | some : A → MyOption A

def first {A : Type} (L : List A) : MyOption A :=
  match L with
  | [] => .none
  | x :: _ => .some x

#eval first [1,2,3]             -- MyOption 1
#eval first ([]:List Int)       -- none
```

Using Option
===

You can use match to get the value of an `Option`, if it exists. 
```lean
def my_func (L : List ℕ) : List ℕ :=
  let x := first L
  match x with
  | .some x => [x,x+1]
  | .none => [0,1]
```

`Option` is an example of a `Monad`. A similar Monad is `Except`, which
also takes a string argument. We'll get to these later.

```lean
#check Except
```

Exercise
===

<ex /> Lean's rational number type `ℚ` defines `1/0` to be `0`. Define a function
`reciprocal (x : ℚ) : Option ℚ` that returns `none` when `x` is zero.



Notation
===

Lean uses notation extensively to make code look more like math.
That's where most symbols come from, in fact. For example, all
operators in the natural numbers are defined as syntax. 
```lean
def MyNat.add (x y : MyNat) :=
  match x with
  | .zero => y
  | .succ k => .succ (MyNat.add k y)

infix:65 " + " => MyNat.add

#eval MyNat.zero.succ + MyNat.zero.succ.succ
```
 The ways in which you can define your own syntax in are many and varied.
We will introduce these mechanisms as we need them.

See the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/#language-extension).



Exercises
===

<ex/> Define a polymorphic tree type `MyTree` where every node may have any number of
children (using List). Define a few example trees demonstrating the features of your datatype.

<ex/> Define a method that maps a function onto the tree. Demonstrate
the method by mapping a function that squares it's argument onto
a tree made of natural numbers.

<ex/> Create a function that converts a `BTree` to a `MyTree`.
Test on your examples.

Exercises
===

<ex/> Consider the *Dyadic Rationals*, which consist of fractions who's denominators
are powers of two defined inductively as follows:


```lean
namespace Temp

inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x
```

a. Define `Dyadic.double` that doubles a `Dyadic`.<br>
b. Define `Dyadic.add` that adds two `Dyadic` values.<br>
c. Define `Dyadic.mul` that multiplies two `Dyadic` values.<br>
d. Define a function `Dyadic.to_rat` that converts a `Dyadic` to a `Rat`.<br>
e. Define the Dyadics `5/8` and `-7/32` and test your methods on these values.<br>
f. Are Dyadics as defined here unique? Why or why not?

```lean
--hide
end Temp
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

