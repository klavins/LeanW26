
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Integers/Definition.lean'>Code</a> for this chapter</span>
 # From Pairs to Integers

As usual when defining a type with the same name as something in the standard library or in Mathlib, we open a namespace to avoid naming conflicts. The `Int` type we define in this section has the fully qualified name `LeanBook.Int`, and is a totally different type than Lean's `Int` type. 
```lean
namespace LeanBook
```
 ## Pairs of Natural Numbers

We first define pairs of natural numbers, recording the components of the pair in a simple structure. Then we define the notion of equivalence that will form the basis of the definition of an integer. 
```lean
@[ext]
structure Pair where
  p : Nat
  q : Nat

def eq (x y: Pair) : Prop := x.p + y.q = x.q + y.p
```
 Here are a few test cases. 
```lean
example : eq ⟨1,2⟩ ⟨2,3⟩ := rfl
example : eq ⟨3,2⟩ ⟨20,19⟩ := rfl
example : ¬eq ⟨3,2⟩ ⟨20,23⟩ := by intro h; simp_all[eq]
```
 ## Equivalence Relations

An **equivalence relation** `≈` is a relation that is

- reflexive: x ≈ x for all x
- symmetric: x ≈ y implies y ≈ x for all x and y
- transitive: x ≈ y and y ≈ z implies x ≈ z for all x, y and z

The relation `eq` defined above is such an equivalence relation. But we have to prove it. This is pretty easy, since it is just some basic arithmetic. 
```lean
theorem eq_refl (u : Pair) : eq u u := by
  simp[eq]
  linarith

theorem eq_symm {v w: Pair} : eq v w → eq w v := by
  intro h
  simp_all[eq]
  linarith

theorem eq_trans {u v w: Pair} : eq u v → eq v w → eq u w := by
  intro h1 h2
  simp_all[eq]
  linarith
```
 With these properties in hand, we can register an instance of `Equivalence`, a Lean 4 standard library class that stores the properties of the equivalence relation in one object, and enables us to easily use any theorems requiring our `eq` relation to have them. 
```lean
instance eq_equiv : Equivalence eq := ⟨ eq_refl, eq_symm, eq_trans ⟩
```
 We can also register `eq` with the `HasEquiv` class, which allows us to use the `≈' notation. 
```lean
@[simp]
instance pre_int_has_equiv : HasEquiv Pair := ⟨ eq ⟩
```
 Here is an example using the new notation. 
```lean
def u : Pair := ⟨ 1,2 ⟩
def v : Pair := ⟨ 12,13 ⟩
#check u ≈ v
```
 Finally, we register `Pair` and `eq` as a `Setoid`, which is a set and an equivalence relation on the set. It is needed for the definition of the quotient space later.  
```lean
instance pre_int_setoid : Setoid Pair :=
  ⟨ eq, eq_equiv ⟩
```
 This exact process should be followed whenever defining a new equivalence class in Lean.

## Quotients

The **equivalence class** of `x` is defined to be the set of all pairs `y` such that `x≈y`. The set of all equivalence classes is called the **quotient space**, which we can form using Lean's `Quotient`:  
```lean
def Int := Quotient pre_int_setoid
```
 We can then construct elements of `Int` using `Quotient.mk`. 
```lean
def mk (w : Pair) : Int := Quotient.mk pre_int_setoid w

#check mk ⟨ 1, 2 ⟩  -- 1
#check mk ⟨ 2, 1 ⟩  -- -1
```
 A key aspect of the quotient space is that equality is extended to elements of the quotient space. Thus, we can write: 
```lean
#check mk ⟨ 1, 2 ⟩ = mk ⟨ 2, 3 ⟩
```
 instead of using `≈`. As a result, we can us all the properties of equality we have become used to with basic types, such as definitional equality and substution.

We may now register a few more classes. The first defines zero, the second defines one, and the third defines a coercion from natural numbers to (non-negative) integers. 
```lean
instance int_zero : Zero Int := ⟨ mk ⟨ 0,0 ⟩ ⟩
instance int_one : One Int := ⟨ mk ⟨ 1,0 ⟩ ⟩
instance int_of_nat {n: ℕ} :OfNat Int n := ⟨ mk ⟨ n, 0 ⟩ ⟩

#check (0:Int)
#check (1:Int)
#check (123:Int)
```
 You may also encounter the notation ⟦⬝⟧ for equivalence classes. Since the notation does not know which equivalence relation you might be talking about, it is only useful in a context where the Type can be inferred.  
```lean
-- Does not work:
#check_failure ⟦⟨1,2⟩⟧

-- Ok:
def my_int : Int := ⟦⟨1,2⟩⟧
```
 ## Using Ints in Proofs

To prove theorems about negation we need some fundamental tools for proving properties of quotients:

- `Quotient.exists_rep`, which says `∃ a, ⟦a⟧ = q`. This operator allows you to assert the existence of a representative of an equivalence class. Then, if you are trying to prove a result about the equivalence class, it amounts to proving it about the representative.

- `Quotient.sound`, which says `a ≈ b → ⟦a⟧ = ⟦b⟧`. Applying this operator allows you to replace a goal involving proving two equivalence classes are equal, with one showing that representatives of the respective equivalence classes are equivalent under the associated Setoid relation. In other words, we _unlift_ the equality back to the underlying space.

Using these two operations, we do a simple proof in which, for illustrative purposes, we write out each step. It is instructive to open this proof in VS Code and examine the proof state before and after each step. 
```lean
example : ∀ x : Int, x = x := by
  intro x
  obtain ⟨ ⟨ a, b ⟩, hd ⟩ := Quotient.exists_rep x
  rewrite[←hd]
  apply Quotient.sound
  simp only [pre_int_setoid,HasEquiv.Equiv,eq]
  exact Nat.add_comm a b
```
 The proof can be made much simpler in this example, because definitional equality is all you need in this case. 
```lean
example : ∀ x : Int, x = x := by
  intro x
  rfl
```
 However, the use of `Quotient.exists_rep` and `Quotient.sound` in the more complicated proofs is often needed, and the above pattern will be applicable in many situations. 

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
