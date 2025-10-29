
Programming in Lean
===

Lean is a full fledged programming language.

Even though people have implemented a web server or robot control code in Lean,
it's intended use is to build proof tools.

In this module we will describe the basics of the language via several examples.

Later, we will show how the language implements the formal mathematics of type theory.



Functions and Variables
===

Here is an example function.

```lean
def f1 (x : Nat) : Nat := x+1
```
 It is called `f1`. It takes one *variable* x.

The type of `x` is `Nat` which is Leans *Natural Number Type*. It can take
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

Rather, an if statement is a first class expression. For example, we can write:

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
  | List.cons x M => x
```
 For example: 
```lean
#eval f5 [1,2,3]
#eval f5 []
```

Recursion
===
A recursive function is one that calls itself. This is incredibly powerful.
To define a recursive function that eventually stops, you have to
call it on a smaller (in some sense) argument each time.

Here is a standard example with `Nat`:


```lean
def fct (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | Nat.succ k => n * (fct k)
```
 And here's another example with `List`: 
```lean
def add_one (L : List Nat) :=
  match L with
  | List.nil => List.nil
  | List.cons x M => List.cons (x+1) (add_one M)
```

When Recusion Doesn't Work
===

Recursion has to be well founded, otherwise you may get an infinite loop,
which Lean does not allow:

```lean
def not_ok (x : Nat) : Nat := not_ok x
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

Functions that Operate on Functions
===

Functions are objects just like anything else. You can pass them as arguments
and return them.

For example:


```lean
def do_twice (f : Nat → Nat) (x : Nat) := f (f x)

#eval do_twice fct 3
```
 And here's another example: 
```lean
def map_list (f : Nat → Nat) (L : List Nat) :=
  match L with
  | List.nil => List.nil
  | List.cons x M => List.cons (f x) (map_list f M)

#eval map_list fct [1,2,3,4,5,6]   -- [1, 2, 6, 24, 120, 720]

def alter (f : Nat → Nat) := fun x => f x + 1

#eval (alter fct) 5        -- 121
```

Tail Recursion
===

They way we wrote `fct` it is *tail recursive*. The expression evaluated
by growing it and then reducing it.

```lean
fct 4 = 4 * (fct 3) = ... = 4*(3*(2*(1*1)))
```

All the fcts have to be resolved before the multiplications
leading to a large intermediate expression in the kernel that takes up a lot of space.

Head Recursion
===

```lean
def factAux (n acc : Nat) : Nat :=
  match n with
  | 0     => acc
  | k+1   => factAux k (acc * (k + 1))
```

The evaluation order is different now because both arguments to
`factAux` have to be evaluated before calling `factAux` again.

```lean
factAux 4 1 = factAux 3 (acc*4)  = factAux 3 4
            = factAux 2 (4*3)    = factAux 2 12
            = factAux 1 (12*2)   = factAux 1 * 24
            = factAux 0 24       = 24
```
But factAux has the wrong signature, so we wrap it


```lean
def fact (n : Nat) : Nat :=
  factAux n 1
```

Local Functions
===

Using `let rec` we can declare a local function aux
to avoid polluting the namespace 
```lean
def fact2 (n : Nat) : Nat :=
  let rec aux (n acc : Nat) : Nat :=
    match n with
    | 0     => acc
    | k+1   => aux k (acc * (k + 1))
  aux n 1
```

A Look Ahead
===

What's cool, is that we can write a proof that these two definitions
yield the same function!

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

Booelans vs Propositions
===

The type `Bool` has possible values true and false.
```lean
#check true
#check false
```
 It is used in programming. It gives a computable value that can be used in downstream
programming logic. For example. 
```lean
def is_even (x : ℕ) : Bool := x % 2 = 0
```
 The type `Prop` has values that are *proofs*. 
```lean
def my_prop := ∀ x : Nat, x ≥ 0
def my_proof := fun x => Nat.zero_le x
theorem my_theorem : my_prop := my_proof

#check my_prop
#check my_proof
#check my_theorem
```

True and False
===

In particular, `True` and `False` are not atomic objects, but inductively
defined types of type Prop. 
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
#eval invert_rat (2/4)
```

Real Numbers
===

Real numbers are a bit different. They are not floating point numbers. They are an
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

```lean
#check 1
#check (1:ℚ)

def toRat (x : ℤ) : ℚ := ↑x
def toRat' (x : ℤ) : ℚ := x
```

Characters and Strings
===

```lean
#check 'u'
#eval 'u'.toNat
#eval Char.mk 117 (by aesop)
#eval 'x'.isLower
#eval 'x'.toUpper

#check "u"
#eval "uw"
#eval "u" ++ "w"
#check String.mk
#eval String.mk ['u','w']
#eval "uw".toUpper
#eval "uw" ≤ "uwece"
```

More about Lists
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
  | List.nil => []
  | List.cons x M => (f x) :: map f M

def map' (f : Nat → Nat) (L : List Nat) :=
  match L with
  | [] => []
  | x :: M => (f x) ::map f M
```

Polymorphism
===

```lean
def map_poly {A : Type} {B : Type} (f : A → B) (L : List A) : List B :=
  match L with
  | List.nil => []
  | List.cons x M => (f x) :: map_poly f M

#eval String.mk (map_poly Char.toUpper ['u','w'])

-- Note A and B above are implicit variables. Lean can infer what they
-- are from the type of f and L. So we put them in curly braces so we don't
-- have to write

def map_poly_explicit (A : Type) (B : Type) (f : A → B) (L : List A) : List B :=
  match L with
  | List.nil => []
  | List.cons x M => (f x) :: map_poly_explicit A B f M

-- and

#eval String.mk (map_poly_explicit Char Char Char.toUpper ['u','w'])

-- Defining your own types : E.g. Binary Trees

-- Defining your own notation

-- Exercise : Write a function takes a character and captializes it if
-- it is a lowercase character
-- leaving non lowercase letters as they are.

end LeanW26
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

