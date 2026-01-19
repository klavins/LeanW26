
Programming in Lean

Lean
===

- Lean is a programming language.
    - People have implemented web servers, robot controllers, etc. code in Lean.
    - But it's intended use is to build proof tools.

- C, Python, Java are *imperative and procedural*
    - Programs describe *how* to do something
    - For loops, sequences of statements, symbol tables

- Lean is declarative and functional
    - Programs define what you want
    - Computation corresponds to the evaluation of functions
    - Recursion instead of procedures

- In this module we will describe the basics of the language via several examples.
- Later, we show how the language implements the formal mathematics of type theory.



Functions
===

Here is an example function.

```lean
def f1 (x : ℕ) : ℕ := x+1
```
 It is called `f1`. It takes one *argument* x.

The type of `x` is `ℕ` which is Lean's *Natural Number Type* (also written `Nat`).
It can take on values 0, 1, 2, 3, ...

The return type of the function is also `ℕ`.

You can (usually) evaluate a function using `#eval`. For example,  
```lean
#eval f1 4
```

If Expressions
===

You can define a new expression using `if`, `then`, and `else`.


```lean
def f2 (x : ℕ) : ℕ :=
  if x < 10
  then 0
  else 1
```
 For example: 
```lean
#eval f2 4
```
 ***Important***: Lean is *not* a procedural language. The above is not interpreted
as telling the CPU which branch to take in some assembly language.

Rather, an `if` statement is a first class expression. For example, we can write:

```lean
#eval (if 3 < 4 then 1 else 2)^2 + (if Even 9 then 3 else 4)
```

Let Expressions
===

Let expressions allow you to define a *bound* variable with a specific value in the
rest of an expression.

```lean
def f3 (x : ℕ) : ℕ :=
  let y := x*x
  y+1

#eval f3 4
```
 Similarly, this is not a control flow situation. For example, you can write: 
```lean
#eval (let x := 5; x*2) + (let x := 3; x-1) -- 12
```

Currying
===

When a function is defined with multiple arguments, as in

```lean
def f4 (x y : ℕ) := 2*x + y
```

it is really being defined as a _a function that takes an argument and returns a function
that takes an argument that returns an expression_. The above is in fact shorthand for:

```lean
def f4' := fun (x : ℕ) => fun (y : ℕ) => 2*x + y
```

Thus, if we just pass one argument to `f4` we a get _partial application_, 
```lean
def f5 := f4 10
```

The function `f5` in this case is equivalent to

```lean
def f5' (y: ℕ) := 20 + y
```

Testing these functions gives:

```lean
#eval f4 10 1    -- 21
#eval f4' 10 1   -- 21
#eval f5 1       -- 21
#eval f5' 1      -- 21
```

Functions that Operate on Functions
===

Functions are objects. You can pass them as arguments
and return them.

For example:


```lean
def do_twice (f : ℕ → ℕ) (x : ℕ) := f (f x)

#check do_twice f1                    -- ℕ → ℕ
#eval do_twice f1 3                   -- 5
#eval do_twice (do_twice f1) 3        -- 7

theorem d2 : do_twice (do_twice f1) 3 = 7 := by
  unfold f1 do_twice
  sorry
```

Unnamed Variables
===

If a function does not use an argument, the Lean linter complains
that you have an unused variable. You can get rid of this with `_` 
```lean
def h1 (x : ℕ) := 1             -- Linter says: unused variable `x`
def h2 (_ : ℕ) := 1
def h3 (_x : ℕ) := 1
```

Exercises
===

<ex/> Define a function `abs_diff` that takes two ℕural numbers and returns the absolute
value of their difference. Use only the constructs defined so far. Evaluate
```lean
#eval abs_diff 23 89
#eval abs_diff 101 89
```
<ex/> Define a function `apply_twice_when_even` that takes a function `f` and a
natural number `x` and returns a function that applies `f` twice if `x` is
even, and once otherwise. Then try these`evals:
```lean
#eval apply_twice_when_even (abs_diff 10) 8
#eval apply_twice_when_even (abs_diff 10) 11
```

(Optional) Show that `abs_diff` is symmetric in its arguments.



Constructors
===

Many types in Lean are defined *inductively* with *constructors*. For example, there are two
ways to make a `ℕ`.

```lean
#print Nat -- constructors:
           -- ℕ.zero : ℕ
           -- ℕ.succ : ℕ → ℕ
```
 You can use the keyword `match` to respond to how a value was constructed.

```lean
def nonzero (x : ℕ) : Bool :=
  match x with
  | Nat.zero => false
  | Nat.succ k => true

#eval nonzero 0
#eval nonzero 1234
```
 Of course this function could also have been written: 
```lean
def nonzero' (x : ℕ) := x ≠ 0
```

Match is a General Pattern Matcher
===

 You just have to cover all possibilities.

In this context, `_` matches anything that hasn't been listed yet. 
```lean
def is_3_or_12 (x : ℕ) : Bool :=
  match x with
  | 3 => true
  | 12 => true
  | _ => false
```
 You can match pairs, triples, etc. 
```lean
def is_3_and_12 (x y : ℕ) : Bool :=
  match x, y with
  | 3, 12 => true
  | _, _ => false
```

If you don't match all possibilities, Lean will give you an error: _Missing cases: ..._


Recursion
===
Recursion is how you do loops in a functional language like Lean.

Here is a standard example with `ℕ`:


```lean
def fct (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | k+1 => n * (fct k)
```
 And here's another example the extends the `do_twice` function: 
```lean
def do_n (n : ℕ) (f : ℕ → ℕ) (x : ℕ) :=
  match n with
  | 0 => x
  | k+1 => f (do_n k f x)

def f10 := do_n 10 f1

#eval f10 0
```

When Recursion Doesn't Work
===

Recursion has to be well founded, otherwise you may get an infinite loop,
which Lean does not allow:

```lean
--def not_ok (x : ℕ) : ℕ := not_ok x
```
 Which results in the error:

> fail to show termination for
  LeanW26.not_ok
> with errors
> failed to infer structural recursion:
> Not considering parameter x of LeanW26.not\_ok:
>   it is unchanged in the recursive calls
> no parameters suitable for structural recursion

> well-founded recursion cannot be used, 'LeanW26.not_ok' does not take any (non-fixed) arguments
```

In other situations, you might define a function that does eventually stop but Lean
may not be able to figure it out, requiring you to also supply a proof
of termination.


Head Recursion
===

They way we wrote `fct`

```lean
def fct (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | ℕ.succ k => n * (fct k)
```

it is *head recursive*. The expression evaluated
by growing it and then reducing it.

```lean
fct 4 = 4 * (fct 3) = ... = 4*(3*(2*(1*1)))
```

All the `fcts` have to be resolved before the multiplications
leading to a large intermediate expression in the kernel that takes up a lot of memory.

Tail Recursion
===

```lean
def factAux (n acc : ℕ) : ℕ :=
  match n with
  | 0     => acc
  | k+1   => factAux k (acc * (k + 1))
```

Now both arguments to `factAux` must be evaluated before calling `factAux` again.

```lean
factAux 4 1 = factAux 3 (acc*4)  = factAux 3 4
            = factAux 2 (4*3)    = factAux 2 12
            = factAux 1 (12*2)   = factAux 1 * 24
            = factAux 0 24       = 24
```
We wrap `factAux` to initialize `acc` and get the desired function. 
```lean
def fact (n : ℕ) : ℕ :=
  factAux n 1

#eval fact 5         -- 120
```

Local Functions
===

Using `let rec` we can declare a local function `aux`
to avoid polluting the namespace. 
```lean
def fact2 (n : ℕ) : ℕ :=
  let rec aux (n acc : ℕ) : ℕ :=
    match n with
    | 0     => acc
    | k+1   => aux k (acc * (k + 1))
  aux n 1

#eval fact2 5

#check fact2.aux
```

The resulting code is usually more compact.


A Look Ahead
===

We can write a proof that these two definitions yield the same function!

```lean
theorem helper (n acc : ℕ) : factAux n acc = acc * fct n := by
  induction n generalizing acc with
  | zero => simp [factAux, fct]
  | succ k ih =>
    unfold factAux fct
    rw[ih (acc*(k+1))]
    apply Nat.mul_assoc

theorem fct_fact : fact = fct := by
  funext n
  unfold fact
  simp[helper n 1]
```
 We'll explain this in a couple of weeks. 

Exercises
===

Recall the Fibonacci sequence is defined by

```lean
  fib 0 = 1
  fib 1 = 1
  fib n = f (n-1) + f (n-2)
```

<ex/> Define `fib` using head recursion. Test it with a few examples.

<ex/> Define `fib` using tail recursion. Test it with a few examples.

Hint: For the tail recursive version, define a helper function that takes
three arguments: `n`, `a` and `b` where `a` and `b` are the previous
two values in the sequence.

(Optional) Prove the two implementations are equivalent.



Booelans vs Propositions
===

`Bool` has possible values `true` and `false`.
```lean
#check true
#check false
```
 It is used in programming. It gives a computable value that can be used in downstream
programming logic. For example. 
```lean
def is_even (x : ℕ) : Bool := x % 2 = 0
```
 `Prop` has values that are *proofs*. 
```lean
def my_prop : Prop := ∀ x : ℕ, x ≥ 0
def my_proof : my_prop := fun x => Nat.zero_le x
theorem my_theorem : my_prop := my_proof

#check my_prop            -- Prop
#check my_proof           -- my_prop
#check my_theorem         -- mp_prop
```

True and False
===

In particular, the `Prop` types `True` and `False` are not atomic objects, but inductively
defined types of type `Prop`. 
```lean
#print True
```

> inductive True : Prop <br>
> number of parameters: 0 <br>
> constructors: <br>
> True.intro : True

```lean
#print False
```

> inductive False : Prop <br>
> number of parameters: 0 <br>
> constructors:

We will have *much* to say about the type `Prop` later in this course.

Like, *a lot* to say.

Really.


Number Types
===

Lean provides a bunch of different types of numbers.

```lean
#check ℕ       -- Natural Numbers
#check ℤ       -- Integers
#check ℚ       -- Rational Numbers
#check ℝ       -- Real Numbers
#check ℂ       -- Complex Numbers
#check Float
#check Float32
```
 Each one has a set of operations on it. For example, you can get the
numerator and denominator of a rational number. 
```lean
def invert_rat (x : ℚ) : ℚ := x.den / x.num

#eval invert_rat (2/4)  -- 2
```
 VS Code will give you completion possibilities for you to explore
if you type a `.` and wait a second.

Real Numbers
===

`Real` numbers are different. They are not floating point numbers. They are an
actual mathematical representations of real numbers (as limits of Cauchy sequences).

Therefore, we can't run  `#eval` on functions involving reals.


```lean
noncomputable
def invert_real (x : ℝ) : ℝ := 1/x
```
 But we can prove theorems about them! 
```lean
theorem invert_invert : invert_real ∘ invert_real = id := by
  funext x
  simp[invert_real]
```

Coercion
===

You can *coerce* a type into another type in a variety of ways, as
long as the type has a defined way to make the conversion. Most
number types are easily coerced.

One way to corece is to use the notation `(value:Type)`.


```lean
#check 1               -- ℕ, the default
#check (1:ℚ)           -- ℚ, coerced to a Rat
```
 These conversions are syntactic sugar for calling an explicit convertor. 
```lean
#check (Rat.ofInt 1)   -- ℚ
```
 If the type of a function is specified, then Lean figures out the conversion
automatically. 
```lean
def toRat (x : ℤ) : ℚ := x
```

Characters and Strings
===

Characters are unicode values with a way to write them as characters under the hood.


```lean
#check 'u'
#eval 'u'.toNat
#eval Char.mk 117 (by aesop)
#eval 'x'.isLower
#eval 'x'.toUpper
```
 Strings are lists of characters. 
```lean
#eval String.ofList ['u','w']
#check "u"
#eval "uw"
#eval "u" ++ "w"
#check String.mk
```
 Strings have a variety of operations 
```lean
#eval "uw".toUpper
#eval "uw" ≤ "uwece"
```

Exercises
===

<ex/> Define a function `mediant (x y : Rat)` that evaluates to the sum
of the numerators over the sum of the denominators of `x` and `y` respectively.

<ex/> Define a function `rep (c : Char) (n : ℕ)` that evaluates to the string consisting
of `n` copies of `c`.




Lists
===
Another example of an inductively defined type is `List`.

Lists are either empty or made by pushing a value onto the
front of some other list.

```lean
#print List -- constructors:
            -- List.nil : {α : Type u} → List α
            -- List.cons : {α : Type u} → α → List α → List α

def f6 (L : List ℕ) : ℕ :=
  match L with
  | List.nil => 0
  | List.cons x _M => x
```
 For example: 
```lean
#eval f6 [1,2,3]  -- 1
#eval f6 []       -- 0
```

List Notation
===

Lists come with various convenient notation.

```lean
#eval [1,2,3]
#eval List.cons 1 (List.cons 2 (List.cons 3 List.nil))
#eval (([].cons 3).cons 2).cons 1
#eval 1 :: 2 :: 3 :: []
```
 For example, here are two ways to write the function `map` which
applies a function to every element in a list.  
```lean
def map (f : ℕ → ℕ) (L : List ℕ) :=
  match L with
  | List.nil => List.nil
  | List.cons x M => List.cons (f x) (map f M)

def map' (f : ℕ → ℕ) (L : List ℕ) :=
  match L with
  | [] => []
  | x :: M => (f x) :: map' f M
```

Polymorphism
===

A `map` function that only works on `ℕ → ℕ` is not very useful. Here's a
*polymorphic* version.

```lean
def map_poly {A : Type} {B : Type} (f : A → B) (L : List A) : List B :=
  match L with
  | List.nil => []
  | List.cons x M => (f x) :: map_poly f M

#eval String.ofList (map_poly Char.toUpper ['u','w'])
```


Here, `map_poly` is a **polymorphic** function and `List A` is a **parameterized** type.

Implicit vs Explicit Variables
===

Note `A` and `B` in

```lean
def map_poly {A : Type} {B : Type} (f : A → B) (L : List A) : List B :=
  match L with
  | List.nil => []
  | List.cons x M => (f x) :: map_poly f M
```

are _implicit_ variables. Lean can infer what they
are from the type of `f` and `L`. So we put them in curly braces so we don't
have to write:

```lean
def map_poly_explicit (A : Type) (B : Type) (f : A → B) (L : List A) : List B :=
  match L with
  | List.nil => []
  | List.cons x M => (f x) :: map_poly_explicit A B f M

#eval String.ofList (map_poly_explicit
                     Char Char Char.toUpper ['u','w'])
```

Other Data Types
===

```lean
#check List       -- Type → Type
#check Vector     -- Type → ℕ → Type
#check Array      -- Type → Type (faster than List, but hard in proofs)
#check Set        -- Type → Type
#check Multiset   -- Type → Type (can contain repeats)
```
 For example: 
```lean
def S1 : Set (Set Char)  := { {'a','b'} }
def S2 : Set (List Char) := { ['a','b'] }
def S3 : List (Set Char) := [ {'a','b'} ]
def S4 : Array (Set Char) := #[ {'a','b'} ]
```
 Later, we'll get to various mathematical types, which are almost always
parameterized in some way: 
```lean
#check Group      -- Type → Type
#check add_comm   -- ∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G),
                  -- a + b = b + a
```

Exercises
===

<ex/> Define a function `rev_list` that reverses a list of any type.

<ex/> Here is a simple sorting algorithm called *insertion sort*. Make a version of this
algorithm that works on any type `α` as long as a comparison function of the form
`lt (x y α) : Bool` is provided as an argument.

 
```lean
def insert (x : ℕ) : List ℕ → List ℕ
| [] => [x]
| y :: ys => if  x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort :  List ℕ → List ℕ
| [] => []
| x :: xs => insert x (insertionSort xs)
```

<ex/> Test your code on the type `String` with the alphabetical ordering defined by


```lean
def str_cmp (a b : String) : Bool := decide (a ≤ b)
```

Exercise (Optional)
===

<ex /> You can solve the insertion sort problem by adding an argument
to `insert` and `insertionSort`
for the comparison function. But the more _Lean_ way to do it is to require
`A` to have instances of `LE` and `DecidableRel` using the `[...]` notation.
Give it a try.

We'll talk about _classes_ and _instances_ next week.

```lean
--hide
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

