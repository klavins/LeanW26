
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Integers/Operators.lean'>Code</a> for this chapter</span>
 # Lifting Operators

In this section we show how to _lift_ an operation, such as negation or addition, from `Pair` to `Int`, and more generally from any type to a quotient on that type. 
 ## Lifting Negation

First, we define the meaning of negation for pairs, which is simply to switch the order of the pair's elements. 
```lean
def pre_negate (x : Pair) : Pair := ⟨ x.q, x.p ⟩
```
 We would like to **lift** the definition of negation to our new `Int` type. This means defining negation of an entire equivalence class, which would only work if our `pre_negate` function has the same result on all elements of an equivalence class, which fortunately it does! To capture this notion we define a _respects_ theorem.  
```lean
theorem pre_negate_respects (x y : Pair) :
  x ≈ y → mk (pre_negate x) = mk (pre_negate y) := by
  intro h
  simp_all[pre_int_setoid,eq]
  apply Quot.sound
  simp[pre_int_setoid,eq,pre_negate,h]
```
 With this theorem, we may use Lean's `Quotient.lift` to define `negate` on `Int`. 
```lean
def pre_negate' (x : Pair) : Int := mk (pre_negate x)

def negate (x : Int) : Int := Quotient.lift pre_negate' pre_negate_respects x
```
 We may register our negation function wit the `Neg` class, allowing us to use the `-` notation for it, and to use any general theorems proved in Mathlib for types with negation.  
```lean
instance int_negate : Neg Int := ⟨ negate ⟩
```
 Now we can use negative integers. 
```lean
#check -mk ⟨2,1⟩
#check -(1:Int)
```
 Here is a simple theorem to test whether all of this is working. 
```lean
theorem negate_negate { x : Int } : -(-x) = x := by
  let ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  simp[pre_int_setoid,pre_negate,eq]
  linarith
```
 ## Lifing Addition

Just as we lifted negation, we can also define and lift addition. For pairs, addition is just componentwise addition. 
```lean
def pre_add (x y : Pair) : Pair := ⟨ x.p + y.p, x.q + y.q ⟩
```
 To do the lift, we need another respects theorey. This time, the theorem assumes multiple equivalences. 
```lean
theorem pre_add_respects (w x y z : Pair)
  : w ≈ y → x ≈ z → mk (pre_add w x) = mk (pre_add y z) := by
  intro h1 h2
  apply Quot.sound
  simp_all[pre_int_setoid,eq,pre_add]
  linarith
```
 With this theorem we can define addition on integers. 
```lean
def pre_add' (x y : Pair) : Int := mk (pre_add x y)

def add (x y : Int) : Int := Quotient.lift₂ pre_add' pre_add_respects x y
```
 And while we are at it, we can register addition with Mathlib's Add class so we can use `+`. 
```lean
instance int_add : Add Int := ⟨ add ⟩
```
 Here is an example. It is remarkable to see that the entire edifice we have built can interact so easily with `rfl`. 
```lean
example : (1:Int) + 17 = 18 := rfl
```
 A slightly more complicated example with addition and negation requires `Quotient.sound` since we have not yet lifted any theorems from `Pair` to `Int`. 
```lean
example : (1:Int) + (-2) = -1 := by
  apply Quotient.sound
  rfl
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
