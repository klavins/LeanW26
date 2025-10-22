
Programming in Lean
===

Lean is a full fledged programming language.

Even though people have implemented a web server or robot control code in Lean,
it's intended use is to build proof tools.


```lean
-- functions and variables
def f1 (x : Nat) := x+1
#eval f1 4

-- if expressions
def f2 (x : Nat) :=
  if x < 10
  then 0
  else 1

#eval f2 4

-- let
def f3 (x : Nat) :=
  let y := x*x
  y+1

#eval f3 4

-- match

#print Nat -- constructors:
           -- Nat.zero : ℕ
           -- Nat.succ : ℕ → ℕ

def f4 (x : Nat) :=
  match x with
  | Nat.zero => 1
  | Nat.succ k => 0

#print List -- constructors:
            -- List.nil : {α : Type u} → List α
            -- List.cons : {α : Type u} → α → List α → List α

def f5 (L : List Nat) :=
  match L with
  | List.nil => 0
  | List.cons x M => x

#eval f5 [1,2,3]
#eval f5 []

-- recursion

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | Nat.succ k => n * (fib k)

def add_one (L : List Nat) :=
  match L with
  | List.nil => List.nil
  | List.cons x M => List.cons (x+1) (add_one M)

-- functions of functions

def do_twice (f : Nat → Nat) (x : Nat) := f (f x)

#eval do_twice fib 3

def map_list (f : Nat → Nat) (L : List Nat) :=
  match L with
  | List.nil => List.nil
  | List.cons x M => List.cons (f x) (map_list f M)

#eval map_list fib [1,2,3,4,5,6]

def alter (f : Nat → Nat) := fun x => f x + 1

#eval (alter fib) 5

-- Loops with lec rec

-- Number Types

-- Lists, Vectors, Strings

-- Option

-- Defining your own types : E.g. Binary Trees

-- Defining your own notation

end LeanW26
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

