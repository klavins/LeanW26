
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

We will redefine some types that Lean defines, so we'll use
a a temporary namespace to avoid collisions:
```lean
namespace Temp
```


Natural Numbers
===

```lean
inductive Nat where
  | zero : Nat               -- base case
  | succ : Nat → Nat         -- recursive constructor

#check Nat                   -- Type

open Nat

#check zero                  -- all Nat
#check succ zero             -- 1
#check succ (succ zero)      -- 2
#check zero.succ
#check zero.succ.succ
```
 This is how you build the natural numbers in Lean. The numerals 0, 1, 2, etc.
are just "syntactic sugar". 
```lean
#eval _root_.Nat.zero == 0
#eval _root_.Nat.zero.succ.succ.succ == 3
```

Complex Numbers
===

All sorts of types are inductive. For example, here is a complex number:

```lean
inductive Complex where
  | mk : Real → Real → Complex

def Complex.re (x : Complex) : Real :=
  match x with
  | mk a _ => a

def Complex.im (x : Complex) : Real :=
  match x with
  | mk _ b => b

#check Complex.mk 1 2

noncomputable
def Complex.abs (x : Complex) : Real := Real.sqrt (x.re^2 + x.im^2)
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

1. Define an alternative complex number in terms of its magnitude and argument.
Note that the type of non-negative reals is defined as `NNReal`.
2. Define `or` for `TriBool`.



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



Defining Functions
===

Here's an example function to convert tree to a list.
It can be refered to as `BTree.to_list` when `BTree` is not open. 
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

1. Define a function `swap` that takes a `BTree` and swaps the order of the
children in all nodes. You should get, for example:

```lean
#eval swap my_tree             -- (1 (3 5 4) 2)
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

1. Define a structure `3DVector`.
2. Define a cross product function of two `3DVectors`.
3. Test on examples.



Products
===

```lean
structure Prod (A B : Type) where
  fst : A
  snd : B

def p : Prod Rat String := ⟨ 0, "zero" ⟩

#eval p.fst
#eval p.snd
```
 Lean's Prod uses `×`: 
```lean
def q : Rat × String := ⟨ 1, "one" ⟩
```

Sums
===

```lean
inductive Sum (A B : Type) where
  | inl : A → Sum A B
  | inr : B → Sum A B

def s1 : Sum Rat String := .inl 0
def s2 : Sum Rat String := .inr "zero"

def swap (s : Sum Rat String) : Sum String Rat :=
  match s with
  | .inl x => .inr x
  | .inr x => .inl x
```
 Lean's Sum uses `⊕`: 
```lean
def s : Rat ⊕ String := .inl 1
#check s
```
 Note: In this example `.inr` and `.inl` refer to `Sum.inr` and `Sum.inl`.
Lean figures out what you mean from the type context. This works for any inductive type. 

Option
===

The `Option` type is useful in situations where a value might not be available.


```lean
inductive Option (A : Type)
  | none : Option A
  | some : A → Option A

def first {A : Type} (L : List A) : Option A :=
  match L with
  | [] => .none
  | x :: _ => .some x

#eval first [1,2,3]             -- Option 1
#eval first ([]:List Int)       -- none
```
 You can use match to get the value of an `Option`, if it exists. 
```lean
def my_func (L : List ℕ) : List ℕ :=
  let x := first L
  match x with
  | .some x => [x,x+1]
  | .none => [0,1]
```

Notation
===

Lean uses notation extensively to make code look more like math.
That's where most symbols come from, in fact. For example, all
operators in the natural numbers are defined as syntax. 
```lean
def my_add (x y : Nat) :=
  match x with
  | .zero => y
  | .succ k => .succ (my_add k y)

infix:65 " + " => my_add

#eval zero.succ + zero.succ.succ
```
 The ways in which you can define your own syntax in are many and varied.
We will introduce these mechanisms as we need them.

See the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/#language-extension).



Exercises
===

1. Define a tree type `MyTree` where every node may have any number of children.
Define an instance of `Repr` for it so you can print it nicely.
Define a method that maps a function onto the tree.
Create a function that converts a `BTree` to a `MyTree`.
Test on examples.

2. Consider the *Dyadic Rationals*, which consist of fractions who's denominators
are powers of two defined inductively as follows:

```lean
inductive Dyadic where
  | zero : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x
```

&nbsp;&nbsp;&nbsp;&nbsp; a. Define `Dyadic.double` that doubles a `Dyadic`.<br>
&nbsp;&nbsp;&nbsp;&nbsp; b. Define `Dyadic.add` that adds two `Dyadic` values.<br>
&nbsp;&nbsp;&nbsp;&nbsp; c. Define a function `Dyadic.to_rat` that converts a `Dyadic` to a `Rat`.<br>
&nbsp;&nbsp;&nbsp;&nbsp; d. Define the Dyadics `5/8` and `-7/32` and test your methods on these values.


Solutions
===

```lean
open Dyadic

def to_rat (x : Dyadic) : Rat := match x with
  | Dyadic.zero =>  0
  | add_one x => to_rat x + 1
  | half x => (to_rat x) / 2
  | neg  x  => -to_rat x

def w := Dyadic.zero.add_one.half.half

#eval to_rat w

def Dyadic.double (x : Dyadic) : Dyadic := match x with
  | Dyadic.zero =>  Dyadic.zero
  | add_one x => add_one (add_one (double x))   -- 2(x+1) = 2x+2
  | half x =>  x                                -- 2(x/2) = x
  | neg  x  => neg (double x)

#eval to_rat (double w)

def Dyadic.dadd (x y : Dyadic) : Dyadic := match x with
  | Dyadic.zero => y
  | add_one z =>  (dadd z y).add_one  -- (z+1) + y = z+y + 1
  | half z => (dadd z y.double).half  -- z/2 + x = (z+2y)/2
  | neg z => (dadd z y.neg).neg       -- (-z)+y = -(z+(-y))

#eval to_rat (dadd w w.double)

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

