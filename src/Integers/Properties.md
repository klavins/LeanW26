
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Integers/Properties.lean'>Code</a> for this chapter</span>
 # Lifting Properties

In this section we show how to lift theorems from a type to a quotient on that type. Continuing with the `Int` example, we lift all the properties required to show that `Int` is an additive group. Then, using Lean's hierarchies, we formally instantiate `Int` as an additive group using these theorems and show how we can then use all of Mathlib's group infrastructure on our new `Int` type.

## Lifting Theorems

There is no direct operator for lifting theorems, but doing so is straightforward. One typically defines a theorem on the base space and then uses it to prove the corresponding theorem on the quotient space. For example, here are several theorems defined on pairs. 
```lean
theorem pre_add_com {x y: Pair} : eq (pre_add x y) (pre_add y x) := by
  simp[eq,pre_add]
  linarith

theorem pre_add_assoc {x y z: Pair}
  : eq (pre_add (pre_add x y) z) (pre_add x (pre_add y z))  := by
  simp[eq,pre_add]
  linarith

theorem pre_zero_add (x : Pair) : eq (pre_add ⟨0,0⟩ x) x := by
  simp[eq,pre_add]
  linarith

theorem pre_inv_add_cancel (x : Pair) : eq (pre_add (pre_negate x) x) ⟨0,0⟩ := by
  simp[eq,pre_negate,pre_add]
  linarith
```
 To lift these theorems to Int, we apply essentially the same pattern to each. We assert the existence of `Pairs` that represent each of the intgers in the target theorem. We substitute those in for the integers. We use `Quot.sound` to restate the goal in terms of pairs. Finally we use the underlying theorem. Here are several examples: 
```lean
theorem add_comm (x y: Int) : x+y = y+x := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  have ⟨ v, hv ⟩ := Quotient.exists_rep y
  rw[←hu,←hv]
  apply Quot.sound
  apply pre_add_com

theorem add_assoc (x y z: Int) : x+y+z = x+(y+z) := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  have ⟨ v, hv ⟩ := Quotient.exists_rep y
  have ⟨ w, hw ⟩ := Quotient.exists_rep z
  rw[←hu,←hv,←hw]
  apply Quot.sound
  apply pre_add_assoc

theorem zero_add (x : Int) : 0 + x = x := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  apply pre_zero_add

theorem inv_add_cancel (x : Int) : -x + x = 0 := by
  have ⟨ u, hu ⟩ := Quotient.exists_rep x
  rw[←hu]
  apply Quot.sound
  apply pre_inv_add_cancel
```
 ## Instantiating the Additive Group Structure on Int

The theorems above were chosen so that we could instantiate a everything we need to show that `Int` forms an additive, commutative group. 
```lean
instance int_add_comm_magma : AddCommMagma Int := ⟨ add_comm ⟩

instance int_add_semi : AddSemigroup Int := ⟨ add_assoc ⟩

instance int_add_comm_semi : AddCommSemigroup Int := ⟨ add_comm ⟩

instance int_group : AddGroup Int :=
  AddGroup.ofLeftAxioms add_assoc zero_add inv_add_cancel
```
 Now we get all the theorems and tactics about additive groups from Mathlib to apply to our `Int` type! For example, 
```lean
example (x: Int) : x-x = 0 := by
  group

example (x y : Int) : x + y - y = x := by
  exact add_sub_cancel_right x y

example (x y z : Int) : x+y+z = x+z+y := by
  calc x+y+z
  _ = x+(y+z) := by rw[add_assoc]
  _ = x+(z+y) := by rw[add_comm y z]
  _ = x+z+y   := by rw[add_assoc]
```
 ## Exercises 
 ## References

The construction here is defined in a number of Algebra textbooks. For an early example, see the Nicolas Bourbaki collective's book _Algebra Part I_, 1943. The English translation of that book from 1974 has the relevant material on page 20. 

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
