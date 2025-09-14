
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/InductiveTypes.lean'>Code</a> for this chapter</span>
 # Inductive Types

As we saw in the chapter on the [λ-Calculus](LambdaCalculus.md), we can encode fairly sophisticated objects like the natural numbers using just abstractions and applications. However, such encodings are a best clunky and hard to read. Additionally, encoding complex data types as λ-Calculus expressions has other problems:

**Noncanonical terms:** The types of such encodings are not guaranteed to result in _canonical_ terms. For example, Church numerals were defined to have type 
```lean
def α := Type
def N := (α → α) → α → α
```
 But we can define expressions that have this type but that do not correspond to natural numbers. For example, 
```lean
def nc : N := λ (f : α  → α) (x : α) => x
```
 It would be vastly preferable if (a) every object of a given type was a legitimate representative of that type and every object also had exactly one representative.

**Pattern Matching and Induction:** To prove properties above objects of a given type, it is useful to apply induction on the structure of the object. For example, a natural number is either zero, or it is the successor of some other natural number. To prove a statement about natural numbers one would like support for pattern matching on the way the number was constructed.

**Termination:** As we have seem, operations on terms of a given type in the pure lambda calculus are not guaranteed to terminate. However, we will see that all terms of a given inductive type support _structural recursion_: We can define functions on that break the term into smaller pieces which eventually lead to indivisible elements, at which point the function terminates.

Thus, Lean and other type theoretic languages include a way to define types inductively. One lists all the ways to construct objects of a given type. Lean then provides a powerful pattern matching capability that can be used in definitions and theorems when operating or reasoning on an object defined inductively.

### Namespaces

In this chapter we will be redefining several fundamental types in Lean, such as the natural numbers `ℕ` and the propositional connectives `And` and `Or`. Since these are part of Lean's standard library (included by default), if we do not take appropriate measures, we will get naming collisions. The easiest way to avoid this is to open a temporary namespace. 
```lean
namespace Temp
```
 Now, when we define a new symbol, such as 
```lean
def Thing := Type
```
 we are actually defining Temp.Thing. If Thing is defined in some inluded library, our new definition will not collide with it.

## Lean's Inductive Types

So far we have introduced only simple **arrow types** composed Lean's basic type (called Type) and functions from those types into types. We now introduce a powerful way to make new types, which covers almost all of mathematics, called **inductive types**.

An inductive type is **generated** by **constructors** that may refer to the type itself. They say how to make objects of the given type.

**Example:** A type with only two elements is defined by: 
```lean
inductive Two where
  | a : Two
  | b : Two

#check Two.a
#check Two.b

def t := Two.a
#eval t
```
 **Example:** The simplest inductive type has _no_ constructors, meaning it specifies the empty type. 
```lean
inductive Empty
```
 ## Constructors With Arguments

You can also have constructors that take arguments and transform them into objects of the given type.

**Example:** The type Nat of **Natural Numbers** is defined by two constructors: 
```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat           -- succ stands for `successor`

open Nat
#check succ (succ (succ zero)) -- 3
```
 All the constructors in an inductively defined type live in a namespace with the same name as the type. The open command allows us to write succ instead of Nat.succ. We can also write 
```lean
#check zero.succ.succ.succ
```
 using so-called dot-notation.

Objects of type `Nat` thus either have the form `zero` or they consist of some finite number of applications of `succ` to the element `zero`. With more types, we can define even more complicated objects.

**Example:** A simple grammar for arithmetic expressions can be defined by the type: 
```lean
inductive Expr where
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr

open Expr
```
 Some example terms include 
```lean
#check add (var "x") (var "y")                          -- x+y
#check add (var "x") (mul (neg (var "y")) (var "z"))    -- x-yz
```
 ## Functions of Inductive Types

To work with objects of inductive types, we usually need to know how the object was constructed. Lean uses the keyword `match` for that.

**Example:** Toggling a Two  
```lean
def Two.toggle ( x : Two ) := match x with
  | a => b
  | b => a
```
 Lean also knows how to reduce expressions involving match. 
```lean
open Two

#reduce toggle (toggle a)
#reduce a.toggle.toggle
```
 **Example:** 1+1 = 2 
```lean
def Nat.plus (n m : Nat) := match n with
  | zero => m
  | succ x => succ (plus x m)

open Nat

#reduce plus (succ zero) (succ zero)  -- zero.succ.succ
```
 **Example:** Swap Adds and Muls
```lean
def Expr.swap (e : Expr) := match e with
  | var s => var s
  | add x y => add y x
  | mul x y => mul y x
  | neg x => neg x


def e := add (var "x") (mul (neg (var "y")) (var "z"))

#reduce e.swap -- -zy+x
```
 ## Inductive Types May Depend on Other Types

The types we have defined so far do not interact with other types. Here's an example that does: Lists of Nats. 
```lean
inductive NatList where
  | empty : NatList
  | cons : Nat → NatList → NatList

namespace NatList

#check cons zero (cons zero empty)              -- [0, 0]
#check (empty.cons zero).cons zero              -- [0, 0]

end NatList

#check [1,2]
```
 Or we can define a List of elements of any type. In the the next bit of code, we implicitly state (using curly braced instead of parens) that List depends on an arbitrary type α. 
```lean
inductive List {α : Type} where
  | empty : List
  | cons : α → List → List

namespace List
#check cons "lean" (cons "is cool" empty)       -- ["lean", "is cool"]
#check cons 3.4 (cons 1.21 empty)               -- [3.14, 1.21]

end List
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
