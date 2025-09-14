
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Numbers.lean'>Code</a> for this chapter</span>
 # The Rational Numbers

<div style='background: yellow'>TODO: This chapter needs to be rewritten to follow the formal of the Integers chapter.</div>

The (pre) rational numbers are just pairs of an `Int` and a `Nat`. But we also have to keep track of whether the denomenator is non-zero. We do that be including in the structure definion the rationals a proof of that property. Thus, every rational number in Lean "knows" it is well-formed. 
```lean
namespace LeanBook

structure PreRat where
  intro ::
  num : Int
  den : Nat
  dnz : den ≠ 0 := by decide -- works with constants

@[simp]
def eq (x y :PreRat) :=
  x.num * y.den = y.num * x.den
```
 Pre-rational admits many representations of the same number. 
```lean
def p12 : PreRat := PreRat.intro 1 2
def p48 : PreRat := PreRat.intro 4 8

example : eq p12 p48 := rfl
```
 Of course, Lean would define notation for all of this. 
 ## Defining the Rationals

One way to define the Rationals from the Pre-Rationals is to form the set of all elements equivalent to a given Pre-Rational. Then that set `is` the rational.

For this to work, we have to show that the equality relation is an `equivalence relation`. This means it needs to be:

  - reflexive: eq x x
  - symmetric: eq x y → eq y x
  - transitive: eq x y ∧ eq y z → eq x z

We define the equivalence class of x to be

  [x] = { y | x = y }

In this case, it is the set of all rationals that reduce to the same number.

The following are equivalent statements

  eq x y
  [x] = [y]
  [x] ∩ [y] = ∅


 ## Equality is Reflexive and Symmetric 
```lean
theorem eq_refl {x : PreRat} : eq x x := by
  rfl

theorem eq_symm {x y : PreRat} : eq x y → eq y x := by
  intro h
  simp[eq]
  rw[eq] at h
  apply Eq.symm
  exact h
```
 ## Transitivity is More Challenging.

We want to show

   x  =  y   and   y  =  z  →  x  =  z

Or

   p     m         m     a      p     a
  ——— = ———  and  ——— = ——— →  ——— = ———
   q     n         q     n      q     b

But we can't use fractions.

To show that x = z, which is equivalent to pb = aq.

We have

   pbn = pnb = mqb = qmb = qan = aqn

   Thus pb = aq since n ≠ 0

   Source: https://math.stackexchange.com/questions/1316069/how-do-i-show-that-the-equivalence-relation-defining-the-rational-numbers-is-tra


 ## Proof of Transitivity 
```lean
theorem eq_trans {x y z : PreRat}
  : eq x y → eq y z → eq x z := by

  intro h1 h2
  let ⟨ p, q, _ ⟩   := x
  let ⟨ m, n, nnz ⟩ := y
  let ⟨ a, b, _ ⟩   := z

  have h : p * b * n = a * q * n := by
    calc p * b * n
    _  = p * ( b * n ) := by rw[Int.mul_assoc]
    _  = p * ( n * b ) := by simp[Int.mul_comm]
    _  = p * n * b     := by rw[Int.mul_assoc]
    _  = m * q * b     := by rw[h1]
    _  = q * m * b     := by simp[Int.mul_comm]
    _  = q * (m * b)   := by simp[Int.mul_assoc]
    _  = q * (a * n)   := by rw[h2]
    _  = q * a * n     := by simp[Int.mul_assoc]
    _  = a * q * n     := by simp[Int.mul_comm]

  simp at h
  apply Or.elim h
  . exact id
  . intro h
    exact False.elim (nnz h)
```
 ## Building the Rationals 
```lean
inductive Rat where
  | of_pre_rat : PreRat → Rat

open Rat

def P12 := of_pre_rat p12
def P48 := of_pre_rat p48
```
 ## Lifting Equality to the Rationals 
```lean
@[simp]
def LiftRel (r : PreRat → PreRat → Prop) (x y : Rat) : Prop :=
  match x, y with
  | of_pre_rat a, of_pre_rat b => r a b

@[simp]
def req := LiftRel eq

example : req P12 P48 := by
  simp[P12,P48,p12,p48]
```
 # Lifting Funtions 
```lean
@[simp]
def pre_negate (x : PreRat) : PreRat := ⟨ -x.num, x.den, x.dnz ⟩

def Respects (f : PreRat → PreRat) := ∀ x y : PreRat, eq x y → eq (f x) (f y)

theorem negate_respects : Respects pre_negate := by
  intro h
  simp_all[pre_negate,eq]

@[simp]
def LiftFun (f : PreRat → PreRat) (x : Rat) : Rat := match x with
  | of_pre_rat a => of_pre_rat (f a)

@[simp]
def negate := LiftFun pre_negate

example : negate (negate P12) = P12 := by
  simp[P12]
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
