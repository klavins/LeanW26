
Example Monad : Maybe
===
In Lean this monad is called `Option`. We'll rebuild it here and call it `Maybe` instead.
The idea is to provide a `none` value when the result of an operation is undefined.

```lean
inductive Maybe (α : Type u) where
  | none : Maybe α
  | some : α → Maybe α

open Maybe
```
 For example, you might ask for the first value of an empty list. 
```lean
def first {α : Type u} (L : List α) : Maybe α := match L with
  | [] => none
  | x::_ => some x

#eval first [] (α := Nat)
#eval first ([] : List Nat)
#eval first [1,2,3]
```

Maybe is Polymorphic
===
Or you might ask for the first character in a string.

```lean
def first_char (s : String) : Maybe Char :=
  if h : s.length > 0 then some s.data[0] else none

#eval first_char "Romeo, Romeo, wherefore art thou Romeo?"
```

Example Monod: Oops
===

Lean does not have a built-in exception handler. But it does have
an `Except` monad. We rebuild it here, but call it `Oops`.


```lean
inductive Oops (α : Type u) where
  | except : String → Oops α
  | ok : α → Oops α

open Oops

def first' {α : Type u} (L : List α) : Oops α := match L with
  | [] => except "Tried to get the first value of an empty list"
  | x::_ => ok x

#eval first' [] (α := Nat)
#eval first' ([] : List Nat)
#eval first' [1,2,3]
```

Non Idomatic Use of Monads
===
Suppose you want to get the first two elements of a list. One thing you could
do is.

```lean
variable {σ : Type u} {α : Type v} {β : Type w}

def first_two' (L : List α) : Maybe (List α) := match L with
  | [] => none
  | x::M => match M with
    | [] => none
    | y::_ => some [x,y]
```
 But this does not really use the power of Monads. 

Chaining Monads
===
Alternatively, you could define a chaining operator `andThen`: 
```lean
def andThen (maybe : Maybe α) (next : α → Maybe β) : Maybe β :=
  match maybe with
  | Maybe.none => none         -- stop here
  | Maybe.some x => next x     -- keep going
```
 Now we can write: 
```lean
def first_two (L : List α) : Maybe (List α) :=
  andThen (first L) (fun x =>
  andThen (first L.tail) (fun y =>
  some [x,y]))

#eval first_two ([]:List Nat)
#eval first_two [10]
#eval first_two [10,20]
#eval first_two [10,20,30,40]
```

Adding Syntax for Chaining
===

We can define notation for chainging to make this even more clear:

```lean
infixl:55 " ~~> " => andThen
```

Now we can see the structure of what we've built more clearly.

```lean
def first_two'' (L : List α) : Maybe (List α) :=
  first L      ~~> fun x =>
  first L.tail ~~> fun y =>
  some [x,y]
```

Exercises
===

<ex/> Define a function `add_firsts` that returns the sum of the first two elements of a list
of natural numbers, if they exist. Use `first_two`, chaining and `List.reverse`.

<ex/> Make another version of this function, but instead of returning `Maybe (List Nat)`,
return an `Oops (List Nat)`.



Registering Maybe as a Monad
===

Our types `Maybe` and `Oops` are not monads yet. We need to instantiate
Lean's `Monad` class first.

Lean's `Monad` class usually just needs two fields instantiated:

- `pure` Takes a value and puts it into the monadic context.
It’s the way to lift a plain value into the monad without adding any effects.

- `bind` Sequences computations. It takes a monadic value and a
function that returns another monadic value, and combines them so that the second computation can depend on the result of the first.

For `Maybe` this works out to:


```lean
instance : Monad Maybe where
  pure x := some x
  bind m next := match m with
    | Maybe.none => none
    | Maybe.some y => next y
```

Lean's Monad Notation
===

Once registered, you can use Lean's `>>=` syntax, which is like our `~~>` syntax.

```lean
def first_two_m (L : List α) : Maybe (List α) :=
  first L      >>= fun x =>
  first L.tail >>= fun y =>
  some [x,y]
```

Do and let
===
You can also use Lean's `do`, which makes the example even
more concise.

```lean
def first_two_do (L : List α) : Maybe (List α) := do
  let x ← first L
  let y ← first L.tail
  some [x,y]

#eval first_two_do [10]
#eval first_two_do [10,20,30]
```

It is tempting to think of this as procedural code. But
it is not. It is just syntax for:

```lean
def first_two (L : List α) : Maybe (List α) :=
  andThen (first L) (fun x =>
  andThen (first L.tail) (fun y =>
  some [x,y]))
```



Exercises
===

<ex/> Retwrite `add_firsts` using `first`, `do` and `let`.

<ex/> Instantiave `Oops` as a monad.


 Monads Defined 
 Another Example : State 
```lean
def Accu (StateType : Type u) (ValueType : Type v) :=
  StateType → StateType × ValueType

namespace Accu

def ok (x : α) : Accu σ α :=
  fun s => (s, x)

def get : Accu σ σ :=
  fun s => (s, s)

def set (s : σ) : Accu σ Unit :=
  fun _ => (s, ())

def andThen (first : Accu σ α) (next : α → Accu σ β) : Accu σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen

def sum_list (L : List Nat) : Nat :=
  let rec aux : List Nat → Accu Nat (List Nat)
    | [] => ok []
    | x::M =>
      aux M  ~~> fun _ =>
      get       ~~> fun z =>
      set (x+z) ~~> fun _ =>
      ok M
  (aux L 0).fst

#eval sum_list [1,2,3,4,5,6]

instance : Monad (Accu α) where
  pure := fun x => ok x
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def sum_list_do (L : List Nat) : Nat :=
  let rec aux : List Nat → Accu Nat (List Nat)
    | [] => ok []
    | x::M => do
      let _ ← aux M       -- side effect is to put sum of values in M in accumulator
      let z ← get         -- assigns z the value of the accumulator, which is the sum of values in M
      let _ ← set (x+z)   -- side effect sets the value of the accumulator to x+z
      ok []               -- returns the accumulator with the empty list in it
  (aux L 0).fst

#eval sum_list_do [1,2,3,4]

def sum_list_for (L : List Nat) : Nat := Id.run do
  let mut s := 0
  for i in L do
    s := s + i
  return s

#eval sum_list_for [1,2,3,4]

def sum_list_simp (L : List Nat) : Nat :=
  match L with
  | [] => 0
  | x::M => x + sum_list_simp M

#eval sum_list_simp [1,2,3,4]

end Accu
```
 Cool example from wikipedia 
 A second situation where List shines is composing multivalued functions. For instance, the nth complex root of a number should yield n distinct complex numbers, but if another mth root is then taken of those results, the final m•n values should be identical to the output of the m•nth root. List completely automates this issue away, condensing the results from each step into a flat, mathematically correct list.[29] 
```lean
end LeanW26.Monads
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

