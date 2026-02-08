 It is important to use implicit arguments for `{x : Spin}` because otherwise
the theorems are not purly equalities or iffs.  
```lean
def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

infix:75 " o " => op

@[simp] theorem op_up_left {x} : up o x = x := by
  cases x <;> rfl

@[simp] theorem op_up_right {x} : x o up = x := by
  cases x <;> rfl

@[simp] theorem op_dn_left {x} : dn o x = x⁻¹ := by
  cases x <;> rfl

@[simp] theorem op_dn_right {x} : x o dn = x⁻¹ := by
  cases x <;> rfl

@[simp] theorem toggle_op_left {x y} : (x o y)⁻¹ = x⁻¹ o y := by
  cases x <;> simp

-- Don't @[simp] this one!
theorem assoc {x y z} : x o (y o z) = (x o y) o z := by
  cases x <;> simp

-- Don't @[simp] this one!
theorem com {x y} : x o y = y o x := by
  cases x <;> simp

theorem toggle_op_right {x y} : (x o y)⁻¹ = y o x⁻¹ := by
  rw[toggle_op_left,com]

theorem inv_cancel_right {x} : x o x⁻¹ = dn := by cases x <;> simp

theorem inv_cancel_left {x} : x⁻¹ o x = dn := by rw[com,inv_cancel_right]



def shift (k x : ℤ) : ℤ := x+k

-- @[simp]
-- theorem shift_inv_right {k} : shift k ∘ shift (-k) = id := by
--   funext x
--   simp[shift]

-- @[simp]
-- theorem shift_inv_left {k} : shift (-k) ∘ shift k = id := by
--   funext x
--   simp[shift]

@[simp]
theorem shift_zero : shift 0 = id := by
  funext x
  simp[shift]

@[simp]
theorem shift_add {j k} : shift k ∘ shift j = shift (j+k) := by
  funext x
  simp[shift]
  linarith

example {k} : Function.Bijective (shift k) := by
  rw[Function.bijective_iff_has_inverse]
  use shift (-k)
  constructor
  · simp[Function.leftInverse_iff_comp]
  · simp[Function.rightInverse_iff_comp]
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

