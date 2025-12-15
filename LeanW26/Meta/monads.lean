import mathlib

namespace LeanW26.Monads

universe u v w

/-
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


-/

/-
Example Monad : Maybe
===
In Lean this monad is called `Option`. We'll rebuild it here and call it `Maybe` instead.
The idea is to provide a `none` value when the result of an operation is undefined.
-/

inductive Maybe (α : Type u) where
  | none : Maybe α
  | some : α → Maybe α

open Maybe

/- For example, you might ask for the first value of an empty list. -/

def first {α : Type u} (L : List α) : Maybe α := match L with
  | [] => none
  | x::_ => some x

#eval first [] (α := Nat)
#eval first ([] : List Nat)
#eval first [1,2,3]

/-
Maybe is Polymorphic
===
Or you might ask for the first character in a string.
-/

def first_char (s : String) : Maybe Char :=
  if h : s.length > 0 then some s.data[0] else none

#eval first_char "Romeo, Romeo, wherefore art thou Romeo?"


/-
Example Monod: Oops
===

Lean does not have a built-in exception handler. But it does have
an `Except` monad. We rebuild it here, but call it `Oops`.

-/

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



/-
Non Idomatic Use of Monads
===
Suppose you want to get the first two elements of a list. One thing you could
do is.
-/

variable {σ : Type u} {α : Type v} {β : Type w}

def first_two' (L : List α) : Maybe (List α) := match L with
  | [] => none
  | x::M => match M with
    | [] => none
    | y::_ => some [x,y]

/- But this does not really use the power of Monads. -/

/-
Chaining Monads
===
Alternatively, you could define a chaining operator `andThen`: -/

def andThen (maybe : Maybe α) (next : α → Maybe β) : Maybe β :=
  match maybe with
  | Maybe.none => none         -- stop here
  | Maybe.some x => next x     -- keep going

/- Now we can write: -/

def first_two (L : List α) : Maybe (List α) :=
  andThen (first L) (fun x =>
  andThen (first L.tail) (fun y =>
  some [x,y]))

#eval first_two ([]:List Nat)
#eval first_two [10]
#eval first_two [10,20]
#eval first_two [10,20,30,40]

/-
Adding Syntax for Chaining
===

We can define notation for chainging to make this even more clear:
-/

infixl:55 " ~~> " => andThen

/-
Now we can see the structure of what we've built more clearly.
-/
def first_two'' (L : List α) : Maybe (List α) :=
  first L      ~~> fun x =>
  first L.tail ~~> fun y =>
  some [x,y]


/-
Exercises
===

<ex/> Define a function `add_firsts` that returns the sum of the first two elements of a list
of natural numbers, if they exist. Use `first_two`, chaining and `List.reverse`.

<ex/> Make another version of this function, but instead of returning `Maybe (List Nat)`,
return an `Oops (List Nat)`.

-/



/-
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

-/

instance : Monad Maybe where
  pure x := some x
  bind m next := match m with
    | Maybe.none => none
    | Maybe.some y => next y

/-
Lean's Monad Notation
===

Once registered, you can use Lean's `>>=` syntax, which is like our `~~>` syntax.
-/

def first_two_m (L : List α) : Maybe (List α) :=
  first L      >>= fun x =>
  first L.tail >>= fun y =>
  some [x,y]

/-
Do and let
===
You can also use Lean's `do`, which makes the example even
more concise.
-/

def first_two_do (L : List α) : Maybe (List α) := do
  let x ← first L               -- This is different than let :=
  let y ← first L.tail
  some [x,y]

#eval first_two_do [10]
#eval first_two_do [10,20,30]

/-
It is tempting to think of this as procedural code. But
it is not. It is just syntax for:

```lean
def first_two (L : List α) : Maybe (List α) :=
  andThen (first L) (fun x =>
  andThen (first L.tail) (fun y =>
  some [x,y]))
```
-/


/-
Exercises
===

<ex/> Retwrite `add_firsts` using `first`, `do` and `let`.

<ex/> Instantiave `Oops` as a monad.

-/



/-
Lean/Mathlib Monads
===

`Option` What we've been calling `Maybe`
`Except` What we've been calling `Oops`.
`Id` The identity monad. Just returns its value.

-/

def doubleM (m : Type → Type) [Monad m] (x : Nat) : m Nat := do
  let y := x * 2
  pure y

#eval doubleM Option 1               -- some 2
#eval doubleM (Except String) 1      -- ok 2
#eval doubleM Id 1                   -- 2

/- Many more: `Reader`, `StateM`, `IO`, `RandomM`. -/

/-
The IO Monad
===
-/

def main : IO Unit := do
  IO.println "Hello!"
  IO.println "This is the IO Monad"
  IO.println "If you run this code from the command line"
  IO.println "you can use IO.getLine"
  IO.println "You can examime the filesystem too."
  let d ← IO.currentDir
  IO.println s!"Current directory: {d}"

#eval main

/-
The List Monad
===
Mathlib adds a Monad instance for lists that allows for nondeterminism.
It is defined something like this

```lean
instance : Monad List where
  pure x := [x]
  bind xs f := xs.foldr (fun a acc => f a ++ acc) []
```

-/

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



/- Cool example from wikipedia -/

/- A second situation where List shines is composing multivalued functions. For instance, the nth complex root of a number should yield n distinct complex numbers, but if another mth root is then taken of those results, the final m•n values should be identical to the output of the m•nth root. List completely automates this issue away, condensing the results from each step into a flat, mathematically correct list.[29] -/

--hide
end LeanW26.Monads
--unhid
