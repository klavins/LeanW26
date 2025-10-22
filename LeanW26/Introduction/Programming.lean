import Mathlib

namespace LeanW26

/-
Programming in Lean
===

Lean is a full fledged programming language.

Even though people have implemented a web server or robot control code in Lean,
it's intended use is to build proof tools.

-/

-- functions and variables
def f1 (x : Nat) : Nat := x+1
#eval f1 4

-- if expressions
def f2 (x : Nat) : Nat :=
  if x < 10
  then 0
  else 1

#eval f2 4

-- let
def f3 (x : Nat) : Nat :=
  let y := x*x
  y+1

#eval f3 4

-- match

#print Nat -- constructors:
           -- Nat.zero : ℕ
           -- Nat.succ : ℕ → ℕ

def f4 (x : Nat) : Nat :=
  match x with
  | Nat.zero => 1
  | Nat.succ k => 0

#print List -- constructors:
            -- List.nil : {α : Type u} → List α
            -- List.cons : {α : Type u} → α → List α → List α

def f5 (L : List Nat) : Nat :=
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

-- Head vs tail recursion
-- This is head recursive
-- fct 4 = 4 * (fct 3) = ... = 4*(3*(2*(1*1)))
-- All the fcts have to be resolved before the multiplications
-- leading to a large intermediate expression in the kernel that takes up a lot of space
def fct (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k+1 => n * (fct k)

-- Here's a head recursive version
-- factAux 4 1 = factAux 3 (acc*4)  = factAux 3 4
--             = factAux 2 (4*3)    = factAux 2 12
--             = factAux 1 (12*2)   = factAux 1 * 24
--             = factAux 0 24       = 24
-- No big intermediate expression
-- But factAux has the wrong signature
def factAux (n acc : Nat) : Nat :=
  match n with
  | 0     => acc
  | k+1   => factAux k (acc * (k + 1))

-- So we wrap it
def fact (n : Nat) : Nat :=
  factAux n 1

-- Using let rec we can declare a local function aux
-- to avoid polluting the namespace
def fact2 (n : Nat) : Nat :=
  let rec aux (n acc : Nat) : Nat :=
    match n with
    | 0     => acc
    | k+1   => aux k (acc * (k + 1))
  aux n 1

lemma t (n acc : Nat) : factAux n acc = acc * fct n := by
  induction n generalizing acc with
  | zero => simp [factAux, fct]
  | succ k ih =>
    unfold factAux fct
    rw[ih (acc*(k+1))]
    apply Nat.mul_assoc

example : fact = fct := by
  funext n
  unfold fact
  simp[t n 1]

/- Booelans vs Propositions

The type `Bool` has possible values true and false.-/

#check true
#check false

/- It is used in programming. It gives a computable value that can be used in downstream
programming logic. For example. -/

def is_even (x : ℕ) : Bool := x % 2 = 0

/- The type `Prop` has values that are *proofs*. -/

def my_prop := ∀ x : Nat, x ≥ 0
def my_proof := fun x => Nat.zero_le x
theorem my_theorem : my_prop := my_proof

#check my_prop
#check my_proof
#check my_theorem

/- In particular, True and False are not atomic objects, but inductively
defined types of type Prop. -/

#check True
#check False


-- Number Types

#check ℕ       -- Nat
#check ℤ       -- Int
#check ℚ       -- Rat
#check ℝ       -- Real
#check ℂ       -- Complex
#check Float
#check Float32

def invert_rat (x : ℚ) : ℚ := x.den / x.num
#eval invert_rat (2/4)

noncomputable
def invert_real (x : ℝ) : ℝ := 1/x

example : invert_real ∘ invert_real = id := by
  funext x
  simp[invert_real]

#print Nat
#print Rat
#print Real

-- Coercion

#check 1
#check (1:ℚ)

def toRat (x : ℤ) : ℚ := ↑x
def toRat' (x : ℤ) : ℚ := x

-- Lists

#eval [1,2,3]
#eval List.cons 1 (List.cons 2 (List.cons 3 List.nil))
#eval (([].cons 3).cons 2).cons 1
#eval 1 :: 2 :: 3 :: []

def map (f : Nat → Nat) (L : List Nat) :=
  match L with
  | List.nil => []
  | List.cons x M => (f x) :: M

def map' (f : Nat → Nat) (L : List Nat) :=
  match L with
  | [] => []
  | x :: M => (f x) :: M

-- Characters and Strings

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



-- Exercise : Write a function takes a character and captializes it if
-- it is a lowercase character
-- leaving non lowercase letters as they are.

-- Polymorphism

-- Defining your own types : E.g. Binary Trees

-- Defining your own notation

end LeanW26
