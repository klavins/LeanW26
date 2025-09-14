
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Add.lean'>Code</a> for this chapter</span>
 # Addition 
```lean
def presum (a b : DCut) :=  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, x+y=z }

theorem presum_ne {a b : DCut} :  ∃ q, q ∈ presum a b := by
  obtain ⟨ x, hx ⟩ := a.ne
  obtain ⟨ y, hy ⟩ := b.ne
  exact ⟨ x+y, ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, by linarith ⟩ ⟩ ⟩ ⟩ ⟩

theorem presum_nf {a b : DCut} : ∃ q, q ∉ presum a b := by
    obtain ⟨ x, hx ⟩ := a.nf
    obtain ⟨ y, hy ⟩ := b.nf
    use x+y
    intro h
    obtain ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, hst ⟩ ⟩ ⟩ ⟩ := h
    have hs' := b_gt_a hs (not_in_a_in_b hx)
    have ht' := b_gt_a ht (not_in_a_in_b hy)
    linarith

theorem presum_op {a b : DCut}
  : ∀ x ∈ presum a b, ∃ y ∈ presum a b, x < y := by
  intro c hc
  simp_all[presum]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := hc
  have hao := a.op
  have hbo := b.op
  obtain ⟨ x', hx', hxx' ⟩ := hao x hx
  obtain ⟨ y', hy', hyy' ⟩ := hbo y hy
  use x'
  apply And.intro
  . exact hx'
  . use y'
    apply And.intro
    . exact hy'
    . linarith

theorem presum_dc {a b : DCut }
  : ∀ (x y : ℚ), x ≤ y ∧ y ∈ presum a b → x ∈ presum a b := by
  intro s t ⟨ h1, h2 ⟩
  simp_all[presum]
  obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩ := h2

  have hyts : y - (t - s) ∈ b.A := by
    have h3 : 0 ≤ t-s := by linarith
    have h4 : y - (t-s) ≤ y := by linarith
    exact b.dc (y-(t-s)) y ⟨h4,hy⟩

  exact ⟨ x, ⟨ hx, ⟨ y - (t-s), ⟨ hyts, by linarith ⟩ ⟩ ⟩ ⟩

def sum (a b : DCut) : DCut :=
  ⟨ presum a b, presum_ne, presum_nf, presum_dc, presum_op ⟩

instance hadd_inst : HAdd DCut DCut DCut:= ⟨ sum ⟩

instance add_inst : Add DCut := ⟨ sum ⟩

theorem add_rats {x y: ℚ} : ofRat (x+y) = ofRat x + ofRat y := by

  simp[ofRat,hadd_inst,sum,presum,odown]
  ext q
  constructor

  . intro hq
    let ε := x+y - q
    have hε : q = x+y-ε := by
      simp[ε]
    simp_all
    exact ⟨ x-ε/2, ⟨ by linarith, ⟨ y-ε/2, ⟨ by linarith, by linarith ⟩ ⟩ ⟩ ⟩

  . intro ⟨ a, ⟨ ha, ⟨ b, ⟨ hb1, hb2 ⟩ ⟩ ⟩ ⟩
    simp_all
    linarith
```
 ### The Associative Property Of Addition 
```lean
theorem sum_assoc {a b c : DCut} : (a+b)+c = a + (b+c) := by
  simp[hadd_inst,sum]
  ext q
  constructor
  . intro hq
    simp_all[presum]
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hsum ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hq
    exact ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  . intro hq
    simp_all[presum]
    obtain ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, hsum ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hq
    exact ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

instance addsemigroup_inst : AddSemigroup DCut := ⟨ @sum_assoc ⟩
```
 ### Commutativity of Addition 
```lean
theorem sum_comm {a b : DCut} : a + b = b + a := by
  simp[hadd_inst,sum]
  ext q
  constructor
  repeat
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩
    exact ⟨ y, ⟨ hy, ⟨ x, ⟨ hx, by linarith ⟩ ⟩ ⟩ ⟩

instance addcommsemigroup_inst : AddCommSemigroup DCut := ⟨ @sum_comm ⟩
```
 ### Adding Zero 
```lean
theorem sum_zero_left {a : DCut} : 0 + a = a := by
  ext c
  simp[hadd_inst,sum,zero_inst]
  constructor
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, h ⟩ ⟩ ⟩ ⟩
    have : x < 0 := hx
    apply a.dc c y
    apply And.intro
    . linarith
    . exact hy
  . intro h
    obtain ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := a.op c h
    have h1 : c-x < 0 := by linarith
    exact ⟨ c-x, ⟨ h1, ⟨ x, ⟨ hx1, by linarith ⟩ ⟩ ⟩ ⟩

theorem sum_zero_right {a : DCut} : a + 0 = a := by
  rw[sum_comm,sum_zero_left]

instance add_zero_inst : AddZeroClass DCut :=
  ⟨ @sum_zero_left, @sum_zero_right ⟩
```
 # Order Properties 
```lean
theorem sum_pos_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  constructor
  . intro h
    have ha0 := pos_has_zero.mp ha
    have hb0 := pos_has_zero.mp hb
    have : 0 ∈ (a+b).A := by
      exact ⟨ 0, ⟨ ha0, ⟨ 0, ⟨ hb0, by exact Rat.zero_add 0 ⟩ ⟩ ⟩ ⟩
    simp[←h,zero_rw,odown] at this
  . intro q hq
    have : q ∈ b.A := by
      simp[zero_rw,odown] at hq
      exact b.dc q 0 ⟨ by linarith, zero_in_pos hb ⟩
    exact ⟨ 0, ⟨ zero_in_pos ha, ⟨ q, ⟨ this, by linarith ⟩ ⟩ ⟩ ⟩

theorem sum_nneg_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  rcases two_nn_ineqs ha hb with ⟨ ha, hb ⟩ | h | h
  . apply lt_imp_le
    apply sum_pos_pos ha hb
  . simp[h,sum_zero_left,hb]
  . simp[h,sum_zero_right,ha]
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
