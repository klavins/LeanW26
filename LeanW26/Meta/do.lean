import mathlib

namespace LeanW26.Do

universe u v w

/-
Review
===
Monads are objects that carry information, may cause side effects, and can be sequenced.
-/

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

/-
Lean's Sequencer `>>=`
===

The `>>=` infix operator is shorhand for `Bind.bind`, which is defined as
```lean
class Bind (m : Type u → Type v)
  bind : {α β : Type u} → m α → (α → m β) → m β
```
Any type instantiated with the `Monad` class, which extends `Bind` can use `>>=`.
-/

def first_two' {α : Type u} (L : List α) :=
  bind (first L)
       (fun x => bind (first L.tail)
                      (fun y => some [x,y]))

/- Is equivalent to -/

def first_two'' (L : List α) :=
  first L      >>= fun x =>
  first L.tail >>= fun y =>
  some [x,y]


/-
Do
===

Carrying all those `>>=` and `fun x =>` expressions around is clunky,
so Lean defines `do` and `let ←` as syntactic sugar.
-/

def first_two''' (L : List α) := do
  let x ← first L
  let y ← first L.tail
  some [x,y]

/- `do` can do even more. -/


/-
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
-/


def f (L : List ℕ) : Id ℕ := do
  let mut s := 0
  if L = []
  then return 0
  else for x in L do
    let y := x*x
    s := s + y
  return s

#eval f [1,2,3]               -- 14

/-
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
-/

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




/-
Monad Transformers
===
A **monad transformer** is a type constructor that layers an effect on
top of an existing monad. It lets you combine effects without writing a custom monad.
-/


#print StateM





/-










asd
===
IO Monad

Example: printing and reading input.
Show equivalence between do and explicit bind.


Option Monad

Example: chaining computations that may fail.
Demonstrate ← for extracting values.




4. Key Features of do

Binding values

x ← expr vs let x := expr.


Ignoring results

Using _ ← expr or just expr.


Returning values

return keyword vs implicit last expression.


Pattern matching in do

Example: match inside do block.




5. Advanced Usage

Combining monads

Example with ExceptT or StateT.


Error handling

Using throw and try/catch in do blocks.


Loops

for and while inside do.




6. Common Pitfalls

Mixing let and ← incorrectly.
Forgetting indentation rules.
Misunderstanding implicit return.


7. Practical Exercises

Implement a small program using IO and Option.
Rewrite a bind-heavy function using do.


8. References

Lean 4 documentation: https://lean-lang.org
Mathlib examples of do usage.

-/

end LeanW26.Do
