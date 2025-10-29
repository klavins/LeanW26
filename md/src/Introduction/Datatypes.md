

We have been using types like Nat, but what is it?

It is any *inductively defined type*:


```lean
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat          -- Type
```

- `zero` is a *constructor*. It takes no arguments and has type `Nat`
- `succ` is a *constructor* that takes one argument, a `Nat`, and returns its successor.

```lean
open MyNat

#check zero                 -- all MyNat
#check succ zero
#check succ (succ zero)
#check zero.succ
#check zero.succ.succ
```
 This is how you build the natural numbers in Lean. The numerals 0, 1, 2, etc.
are just "syntactic sugar". 
```lean
#eval Nat.zero == 0
#eval Nat.zero.succ.succ.succ == 3
```


You can make lots of types inductive. For example, here is an complex number:


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


And here is three valued logic Boolean:


```lean
inductive TriBool where
  | t : TriBool
  | f : TriBool
  | un : TriBool

open TriBool

def and (A B : TriBool) :=
  match A, B with
  | t, t   => t
  | t, f   => f
  | t, un  => un
  | f, t   => f
  | f, f   => f
  | f, un  => f
  | un, t  => un
  | un, f  => f
  | un, un => un

#eval and t (and f un)
```


Here is a an extended example where we define a polymorphic Binary Tree type.


```lean
inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : A → BTree A → BTree A → BTree A

open BTree

def to_str {A : Type} [sa : ToString A] (T : BTree A) : String :=
  match T with
  | leaf a => toString a
  | node a L R =>  "(" ++ (toString a) ++ " " ++ (to_str L) ++ " " ++ (to_str R) ++ ")"

instance {A : Type} [Repr A] [ToString A]: Repr (BTree A) := {
  reprPrec := fun T x => to_str T
}

def my_tree := node 1 (leaf 2) (node 3 (leaf 4) (leaf 5))

def to_list {A : Type} (T : BTree A) : List A :=
  match T with
  | leaf a => [a]
  | node a left right => [a] ++ (to_list left) ++ (to_list right)

#eval to_list my_tree
#eval to_list (node 0 my_tree my_tree)

def bt_map {A B : Type} (f : A → B) (T : BTree A) : BTree B :=
  match T with
  | leaf a => leaf (f a)
  | node a left right => node (f a) (bt_map f left) (bt_map f right)

#eval bt_map (fun x => x*x) (node 0 my_tree my_tree)
```


Recall the pattern for MyComplex in which we

- defined an inductive type with a constructor of the form A → A → A
- defined accessors with match x with | mk x y = x.

That is so common that Lean has a convenience notation.

If you have an inductive type with *one* constructor, then you can use a *structure*.


```lean
structure LessComplex where
  re : Real
  im : Real

open LessComplex

def conj (x : LessComplex) : LessComplex:= {
  re := x.re,
  im := -x.im
}
```


Q: Why do you think this doesn't work

```lean
def conj (x : LessComplex) := {
  re := x.re,
  im := -x.im
}
```

 Bracket notation for structures.

You can also use notation like ⟨ a, b ⟩ if the type is known. For example


```lean
def add (x y : LessComplex) : LessComplex :=
  ⟨ x.re + y.re, x.im + y.im ⟩
```

  You can still use structures as though they were inductive types (since they are).
  For example, match still works. For example, here are several ways to define negate.

```lean
def negate1 (x : LessComplex) := LessComplex.mk (-x.re) (-x.im)

def negate2 (x : LessComplex) : LessComplex := { re := -x.re, im:= -x.im }

def negate3 (x : LessComplex) : LessComplex := ⟨ -x.re, -x.im ⟩

def negate4 (x : LessComplex) : LessComplex :=
  match x with
  | mk a b => ⟨ -a, -b ⟩

def negate5 (x : LessComplex) : LessComplex :=
  match x with
  | ⟨ a, b ⟩ => ⟨ -a, -b ⟩

def negate6 (x : LessComplex) : LessComplex :=
  match x with
  | { re := a, im := b } => ⟨ -a, -b ⟩

def negate7 (x : LessComplex) : LessComplex := ⟨ -x.1, -x.2 ⟩
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

