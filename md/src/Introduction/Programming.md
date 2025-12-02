
Programming in Lean
===

- Lean is a programming language.
    - People have implemented web servers, robot controllers, etc. code in Lean.
    - But it's intended use is to build proof tools.

- C, Python, Java are *immperative and procedural*
    - Programs describe *how* to do something
    - For loops, sequences of statements, symbol tables

- Lean is declarative and functional
    - Programs define what you want
    - Computation corresponds to the evaluation of functions
    - Recursion instead of procedues

- In this module we will describe the basics of the language via several examples.
- Later, we show how the language implements the formal mathematics of type theory.



Functions
===

Here is an example function.

```lean
def f1 (x : Nat) : Nat := x+1
```
 It is called `f1`. It takes one *argument* x.

The type of `x` is `Nat` which is Lean's *Natural Number Type*. It can take
values 0, 1, 2, 3, ...

The return type of the function is also `Nat`.

You can (usually) evaluate a function using `#eval`. For example,  
```lean
#eval f1 4
```

If Expressions
===

You can define a new expression using `if`, `then`, and `else`.


```lean
def f2 (x : Nat) : Nat :=
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
#eval (if 3 < 4 then 1 else 2)^2 + (if Even 9 then 3 else 4) -- 5
```

Let Expressions
===

Let expressions allow you to define a *bound* variable with a specific value in the
rest of an expression.

```lean
def f3 (x : Nat) : Nat :=
  let y := x*x
  y+1

#eval f3 4
```
 Similarly, this is not a control flow sitation. For example, you can write: 
```lean
#eval (let x := 5; x*2) + (let x := 3; x-1) -- 12
```

Functions that Operate on Functions
===

Functions are objects. You can pass them as arguments
and return them.

For example:


```lean
def do_twice (f : Nat → Nat) (x : Nat) := f (f x)

#check do_twice f1                  -- ℕ → ℕ
#eval do_twice f1 3                 -- 5
#eval do_twice (do_twice f1) 3      -- 7
```

Unamed Variables
===

If a function does not use an argument, the Lean linter complains
that you have an unused variable. You can get rid of this with `_` 
```lean
def h1 (x : Nat) := 1             -- unused variable `x`
def h2 (_ : Nat) := 1
def h3 (_ : Nat) := 1
```

Exercises
===

<ex/> Define a function `abs_diff` that takes two natural numbers and returns the absolute
value of their difference. Use only the contructs defined so far. Evaluate
```lean
#eval abs_diff 23 89
#eval abs_diff 101 89
```
<ex/> Define a function `apply_twice_when_even` that takes a function `f` and a natural number `x`
and returns a function that applies `f` twice if `x` is even, and once otherwise.
```lean
#eval apply_twice_when_even (abs_diff 10) 8
#eval apply_twice_when_even (abs_diff 10) 11
```


Constructors
===

Many types in Lean are defined *inductively* with *constructors*. For example, there are two
ways to make a `Nat`. 
```lean
#print Nat -- constructors:
           -- Nat.zero : ℕ
           -- Nat.succ : ℕ → ℕ
```
 You can use the keyword `match` to check how a value was constructed. 
```lean
def nonzero (x : Nat) : Bool :=
  match x with
  | Nat.zero => false
  | Nat.succ k => true

#eval nonzero 0
#eval nonzero 1234
```
 Of course this function could also have been written: 
```lean
def nonzero' (x : Nat) := x ≠ 0
```

Match is a General Pattern Matcher
===

 You just have to cover all possibilities. `_` matches everything. 
```lean
def is_3_or_12 (x : Nat) : Bool :=
  match x with
  | 3 => true
  | 12 => true
  | _ => false
```
 You can match pairs, triples, etc. 
```lean
def is_3_and_12 (x y : Nat) : Bool :=
  match x, y with
  | 3, 12 => true
  | _, _ => false
```

Recursion
===
Recursion is how you do loops in a functional language like Lean.

Here is a standard example with `Nat`:


```lean
def fct (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | Nat.succ k => n * (fct k)
```
 And here's another example with: 
```lean
def do_n (n : Nat) (f : Nat → Nat) (x : Nat) :=
  match n with
  | 0 => x
  | Nat.succ k => f (do_n k f x)

def f10 := do_n 10 f1

#eval f10 0
```

When Recursion Doesn't Work
===

Recursion has to be well founded, otherwise you may get an infinite loop,
which Lean does not allow:

```lean
--def not_ok (x : Nat) : Nat := not_ok x
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

They way we wrote `fct` it is *head recursive*. The expression evaluated
by growing it and then reducing it.

```lean
fct 4 = 4 * (fct 3) = ... = 4*(3*(2*(1*1)))
```

All the `fcts` have to be resolved before the multiplications
leading to a large intermediate expression in the kernel that takes up a lot of memory.

Tail Recursion
===

```lean
def factAux (n acc : Nat) : Nat :=
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
def fact (n : Nat) : Nat :=
  factAux n 1
```

Local Functions
===

Using `let rec` we can declare a local function `aux`
to avoid polluting the namespace. 
```lean
def fact2 (n : Nat) : Nat :=
  let rec aux (n acc : Nat) : Nat :=
    match n with
    | 0     => acc
    | k+1   => aux k (acc * (k + 1))
  aux n 1

#eval fact2 5         -- 120
```
 The resulting code is usually more compact. 

A Look Ahead
===

We can write a proof that these two definitions yield the same function!

```lean
lemma helper (n acc : Nat) : factAux n acc = acc * fct n := by
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
def my_prop : Prop := ∀ x : Nat, x ≥ 0
def my_proof : my_prop := fun x => Nat.zero_le x
theorem my_theorem : my_prop := my_proof

#check my_prop
#check my_proof
#check my_theorem
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
#check ℕ       -- Nat
#check ℤ       -- Int
#check ℚ       -- Rat
#check ℝ       -- Real
#check ℂ       -- Complex
#check Float
#check Float32
```
 Each one has a set of operations on it. For example, you can get the
numerator and denominator of a rational number. 
```lean
def invert_rat (x : ℚ) : ℚ := x.den / x.num

#eval invert_rat (2/4)  -- 2
```

Real Numbers
===

`Real` numbers are different. They are not floating point numbers. They are an
actual mathematical representations of real numbers (as limits of Cauchy sequences,
if you must know).

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

<ex/> Define a function `my_sum (x y : Rat)` that evalutes to the sum of `a` and `b`. Use the
numerator and denominator of `a` and `b`.

<ex/> Define a function `rep (c : Char) (n : Nat)` that evaluates to the string consisting
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

def f5 (L : List Nat) : Nat :=
  match L with
  | List.nil => 0
  | List.cons x _M => x
```
 For example: 
```lean
#eval f5 [1,2,3]
#eval f5 []
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
applies a function to evey element in a list.  
```lean
def map (f : Nat → Nat) (L : List Nat) :=
  match L with
  | List.nil => List.nil
  | List.cons x M => List.cons (f x) (map f M)

def map' (f : Nat → Nat) (L : List Nat) :=
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

Implicit vs Explicity Variables
===

Note `A` and `B` above are implicit variables. Lean can infer what they
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
def insert (x : Nat) : List Nat → List Nat
| [] => [x]
| y :: ys => if  x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort :  List Nat → List Nat
| [] => []
| x :: xs => insert x (insertionSort xs)
```

<ex/> Test your code on the type `String` with the alphabetical ordering defined by

```lean
def str_cmp (a b : String) : Bool := decide (a ≤ b)

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

