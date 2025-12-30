
Monads
===
Monads are
- a data type that allows for sequencing, side effects, and off-path
information.
- a way to make functional programming look like procedural programming
- supported by deep math, especially category theory

Lean implements Monads extensively in its metaprogramming framework.

Other languages that use Monads are: Haskell, Agda, F#, OCaml.
Languages with Monad like libraries include: Scala, Rust, Javascript (promises),




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
  let x ← first L               -- This is different than let :=
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



Lean/Mathlib Monads
===

`Option` What we've been calling `Maybe`
`Except` What we've been calling `Oops`.
`Id` The identity monad. Just returns its value.


```lean
def doubleM (m : Type → Type) [Monad m] (x : Nat) : m Nat := do
  let y := x * 2
  pure y

#eval doubleM Option 1               -- some 2
#eval doubleM (Except String) 1      -- ok 2
#eval doubleM Id 1                   -- 2
```
 Many more: `Reader`, `StateM`, `IO`, `RandomM`. 

The IO Monad
===

```lean
def main : IO Unit := do
  IO.println "Hello!"
  IO.println "This is the IO Monad"
  IO.println "If you run this code from the command line"
  IO.println "you can use IO.getLine"
  IO.println "You can examime the filesystem too."
  let d ← IO.currentDir
  IO.println s!"Current directory: {d}"

#eval main
```

The List Monad
===
Mathlib adds a Monad instance for lists that allows for nondeterminism.
It is defined something like this

```lean
instance : Monad List where
  pure x := [x]
  bind xs f := xs.foldr (fun a acc => f a ++ acc) []
```


```lean
def pairs : List (Nat × Nat) := do
  let a ← [1, 2]
  let b ← [3,4,5]
  pure (a, b)

#eval pairs

def prods : List Nat := do
  let a ← [1, 2]
  let b ← [3,4,5]
  let c ← [6,7]
  pure (a*b*c)

#eval prods



import mathlib

namespace LeanW26.Do

universe u v w
```

Review
===
Monads are objects that carry information, may cause side effects, and can be sequenced.

```lean
variable {α : Type u} {β : Type v}

def first (L : List α) : Option α := match L with
  | [] => none
  | x::_ => some x

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

infixl:55 " ~~> " => andThen

def first_two (L : List α) :=
  first L      ~~> fun x =>
  first L.tail ~~> fun y =>
  some [x,y]
```

Sequencing
===

The `>>=` infix operator is shorthand for `Bind.bind`, which is defined as
```lean
class Bind (m : Type u → Type v)
  bind : {α β : Type u} → m α → (α → m β) → m β
```
Any type instantiated with the `Monad` class, which extends `Bind` can use `>>=`.

```lean
def first_two' {α : Type u} (L : List α) :=
  bind (first L)
       (fun x => bind (first L.tail)
                      (fun y => some [x,y]))
```
 Is equivalent to 
```lean
def first_two'' (L : List α) :=
  first L      >>= fun x =>
  first L.tail >>= fun y =>
  some [x,y]
```

Do
===

Carrying all those `>>=` and `fun x =>` expressions around is clunky,
so Lean defines `do` and `let ←` as syntactic sugar.

```lean
def first_two''' (L : List α) := do
  let x ← first L
  let y ← first L.tail
  some [x,y]
```
 `do` can do even more. 

Do Block Structure
===

```lean
do
  stmt₁
  stmt₂
  ...
  stmtₙ
```

where `stmtᵢ` is one of the following

```
let ←            return           if
let :=           pure             match
let mut                           for
```

Or any expression returning `Unit`, such as `IO.println`.

Example Do Block
===

Here is an example that computes the sum of squares of a list of numbers.

```lean
def f (L : List ℕ) : Id ℕ := do
  let mut s := 0
  if L = []
  then return 0
  else for x in L do
    let y := x*x
    s := s + y
  return s

#eval f [1,2,3]               -- 14
```

- `s` is a *mutable* variable and gets reassigned.
- `for`, `in`, `do` is syntax for
- `return` isn't needed, but looks good.
- The monad being used ins `Id ℕ`. Try changing it to `Option ℕ` or `Execpt String ℕ`.

Note that `y := x*x` is a *pure binding*, meaning it is equivalence to `y ← pure (x*x)`.
You could also do `y ← x*x`. Lean would coerce this to `y → pure (x*x)`
which is equivalence to `y := x*x`.



The StateM Monad
===

The StateM monad is defined as

```lean
def StateM (σ α : Type) := σ → (α × σ)
```

It takes an *input* state and returns a *value* and an *updated state*.

The Monad instance for `StateM` is defined by
```lean
instance (σ α : Type) : Monad StateM σ α :=
  pure (x : α) := fun s => (x,s)
  bind (ma : StateM σ α) (f : α → StateM σ α := fun s => f s (ma s)
```

It has associated methods:
- `get : StateM σ σ` — read the current state
- `set : σ → StateM σ Unit` — overwrite the state
- `modify : (σ → σ) → StateM σ Unit` — apply a state update
- `run : StateM σ α → σ → (α × σ)` — execute with initial state

StateM Examples
===

```lean
def tick : StateM Nat Nat := do
  let s ← get     -- get the value
  set (s + 1)     -- change the state to the value + 1
  return s        -- return the (value,state) pair

#eval (do
  let _ ← tick
  let _ ← tick
  let r ← tick
  return r
).run 0            -- (2,3)

def push {α : Type} (x : α) : StateM (List α) Unit := do
  modify (fun xs => x :: xs)

#eval (do
  push 1
  push 0
).run [3,4,5]     -- [0,1,2,3,4,5]
```

Exercises
===


Monad Transformers
===
A **monad transformer** is a type constructor that layers an effect on
top of an existing monad. It lets you combine effects without writing a custom monad.


Exercises
===


```lean
end LeanW26.Do


--hide
end LeanW26.Monads
--unhid
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

