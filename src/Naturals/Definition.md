
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Naturals/Definition.lean'>Code</a> for this chapter</span>
 # The Natural Numbers and Hierarchies

In the chapter on inductive types, we encountered the natural numbers. So to some extent, we are done defining them. But the natural numbers have many, many properties that are incredibly useful over a huge range of mathematics. In fact, defining them is the easy part. Understanding their structure is much more interesting.

In this chapter, we will define the natural numbers and develop some of their algebraic and ordering structure. Along the way, we show how Lean's **hierarchy** system works. Hierarchies are useful for proving general theorems about algebreic structures that can be reused in specific instances. For example, consider associative property: `(x+y)+z = x+(y+z)`. This property holds for natural numbers, integers, rationals, reals, matrices, polynomials, and many more objects. And it leads to many auxilliary theorems, such as `(w+x)+(y+z) = (w+(x+y))+z` and so on. Rather than proving all all these theorems for a new type, we just prove a few basic theorems, like associativity and a few others, and then do some book-keeping to connect our new type to the hige list of theorems that hold for similar objects.

## The Inductive Definition of the Natural Numbers

As we've seen, the Natural Numbers are defined inductively. We open the a temporary namespace, `Temp` to avoid naming conflicts with Lean's standard `Nat` type. So, in the below, every time you see `Nat`, it means `Temp.Nat`. 
```lean
#check Nat.succ_add

theorem succ_add_eq_add_succ' (a b : Nat) : Nat.succ a + b = a + Nat.succ b := by
  apply Nat.succ_add

example (j k: Nat) : j.succ + k = j + k.succ := by exact Nat.succ_add_eq_add_succ j k

#check Nat.succ_add_eq_add_succ

namespace Temp

-- Definition
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat
```
 Using this definition, it is straightfoward to define addition and multiplication. 
```lean
def Nat.add (n m: Nat) : Nat := match m with
  | zero => n
  | succ k => succ (add n k)

-- def Nat.add (n m: Nat) : Nat := match n,m with
--   | a, Nat.zero   => a
--   | a, Nat.succ b => Nat.succ (Nat.add n m)

def Nat.mul (n m: Nat) : Nat := match n with
  | zero => zero
  | succ k => add (mul k m) m     -- (k+1)*m = k*m+m
```
 ## First Use of Lean's Classes

If you have a type for which things like zero, one, addition, and multiplication are defined, it would be nice to use the notation 0, 1, + and *. Although you could use Lean's `syntax` and `infix` operators to define such notation, it is better practice to **instantiate** the **classes** that group all types that have zero, one, addition and multiplication. To do this, we use the `instance` keyword and various classes, such as `Zero`, `One`, `Add` and `Mul` defined in Lean's standard library or in Mathlib.

Here are several examples: 
```lean
instance inst_zero : Zero Nat := ⟨ zero ⟩         -- Zero
instance inst_one : One Nat := ⟨ succ zero ⟩      -- One
instance inst_add : Add Nat := ⟨ add ⟩            -- Addition
instance inst_hadd : HAdd Nat Nat Nat := ⟨ add ⟩  -- Extra hints with addition
instance inst_mul : Mul Nat := ⟨ mul ⟩            -- Multiplication
```
 Now we can do a few examples using the notation. Note that in these examples, we have to give Lean some hints that we are working with our `Temp.Nat` type. Otherwise it assumes numbers like `0` and `1` refer to the build in Nat type.  We do this by coercing one of the terms in our expressions, as in `(1:Nat)`. 
```lean
example : (1:Nat) + 0 = 1 := rfl
example : (1:Nat) * 0 = 0 := rfl
```
 ## Properties of Addition and Multiplication

With this notation, we can cleanly express some of the basic properties of the natural numbers and start working on proofs. These theorems may seem very basic, but together they form the basis of automated proof checking with the natural numbers, connecting results about, for example, cryptography, with the type-theoretic foundations of mathematics.

Most of these theorems can be found in Lean's standard library. But it is interesting to reproduce them here to understand how the theory is constructed. 
```lean
#check AddSemiconjBy.eq
#check congrArg

theorem succ_add (n m : Nat) : (succ n) + m = succ (n + m) := by
  induction m with
  | zero => rfl
  | succ k ih => apply congrArg succ ih

theorem succ_add_eq_add_succ (a b : Nat) : succ a + b = a + succ b := by
  apply succ_add

theorem add_zero_zero_add {x: Nat} : 0+x=x+0 := by
  induction x with
    | zero => rfl
    | succ j ih =>
      apply congrArg succ ih

theorem zero_add {x : Nat} : 0+x = x := by
  induction x with
    | zero => rfl
    | succ j ih =>
      apply congrArg succ ih

theorem add_comm (x y : Nat) : x+y = y+x := by
  induction x with
  | zero => exact add_zero_zero_add
  | succ k ih =>
    have : y + k.succ = (y + k).succ := rfl
    rw[this,←ih]
    have : k + y.succ = (k+y).succ := rfl
    rw[←this]
    exact succ_add_eq_add_succ k y

theorem add_zero (x : Nat) : x+0 = x := by
  rw[add_comm,zero_add]

theorem succ_add_one (x : Nat) : x.succ = x + 1 := by
  induction x with
  | zero => rfl
  | succ k ih =>
    conv => lhs; rw[ih]
    rfl

theorem add_assoc (x y z : Nat) : x+y+z = (x+y)+z := sorry
```
 ## Ordering Properties of Nat 
```lean
def Nat.leb (x y : Nat) : Bool := match x,y with
  | zero,zero => true
  | succ _,zero => false
  | zero,succ _ => true
  | succ k, succ j => leb k j

def Nat.le (x y : Nat) : Prop := leb x y = true

instance inst_dec_le : DecidableRel le := by
  intro x y
  match x with
  | zero =>
    match y with
    | zero => exact isTrue rfl
    | succ k => exact isTrue rfl
  | succ k =>
    match y with
    | zero =>
      unfold le
      exact isFalse Bool.false_ne_true
    | succ j  =>
      unfold le
      exact (k.succ.leb j.succ).decEq true

def Nat.lt (x y: Nat) : Prop := le x y ∧ x ≠ y

instance inst_le : LE Nat  := ⟨ le ⟩

instance inst_lt : LT Nat  := ⟨ lt ⟩

#eval le (1:Nat) 0

def Nat.min (x y: Nat) : Nat := if le x y then x else y

instance inst_min : Min Nat  := ⟨ min ⟩

instance inst_max : Max Nat  := ⟨ sorry ⟩

instance inst_ord : Ord Nat  := ⟨ sorry ⟩

instance inst_preo : Preorder Nat  := ⟨ sorry, sorry, sorry ⟩

instance inst_po : PartialOrder Nat  := ⟨ sorry ⟩

instance inst_lo : LinearOrder Nat := ⟨
  sorry,
  by exact inst_dec_le,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry ⟩
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
