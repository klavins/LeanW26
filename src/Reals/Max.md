
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Max.lean'>Code</a> for this chapter</span>
 # The Maximum Operator 
```lean
theorem neg_gt_zero {a : DCut} (ha : a < 0) : 0 < -a := by

  simp[lt_inst]
  apply And.intro

  . intro h
    obtain ⟨ h1, h2 ⟩ := ha
    exact h1 h

  . intro q hq
    simp[zero_rw,odown] at hq
    simp[neg_inst,neg,preneg]
    obtain ⟨ b, hb ⟩ := a.nf
    exact ⟨ q, ⟨ hq, ⟨ 0, ⟨ zero_notin_neg ha, Eq.symm (sub_zero q) ⟩ ⟩ ⟩ ⟩

theorem maximum_ne {a b : DCut} : ∃ q, q ∈ a.A ∪ b.A := by
  obtain ⟨ x, hx ⟩ := a.ne
  use x
  exact Set.mem_union_left b.A hx

theorem maximum_nf {a b : DCut} : ∃ q, q ∉ a.A ∪ b.A := by
  obtain ⟨ x, hx ⟩ := a.nf
  obtain ⟨ y, hy ⟩ := b.nf
  apply Or.elim (trichotomy a b)
  . intro h
    simp_all
    use y
    apply And.intro
    . intro h1
      exact hy (h h1)
    . exact hy
  . intro h
    apply Or.elim h
    . intro h1
      simp[h1]
      use y
    . intro h1
      simp[h1]
      use x
      exact ⟨ hx, fun a ↦ hx (h1 a) ⟩

theorem maximum_dc {a b : DCut} : ∀ (x y : ℚ), x ≤ y ∧ y ∈ a.A ∪ b.A → x ∈ a.A ∪ b.A := by
  intro x y ⟨ hx, hy ⟩
  apply Or.elim hy
  . intro h
    simp[h]
    exact Or.inl (a.dc x y ⟨ hx, h ⟩)
  . intro h
    simp[h]
    exact Or.inr (b.dc x y ⟨ hx, h ⟩)

theorem maximum_op {a b : DCut} : ∀ x ∈ a.A ∪ b.A, ∃ y ∈ a.A ∪ b.A, x < y:= by
  intro x hx
  apply Or.elim hx
  . intro h
    obtain ⟨ q, ⟨ hq1, hq2 ⟩ ⟩ := a.op x h
    exact ⟨ q, ⟨ Set.mem_union_left b.A hq1, hq2 ⟩ ⟩
  . intro h
    obtain ⟨ q, ⟨ hq1, hq2 ⟩ ⟩ := b.op x h
    exact ⟨ q, ⟨ Set.mem_union_right a.A hq1, hq2 ⟩ ⟩

def maximum (a b : DCut) : DCut :=
 ⟨ a.A ∪ b.A, maximum_ne, maximum_nf, maximum_dc, maximum_op ⟩

instance max_inst : Max DCut := ⟨ maximum ⟩

theorem max_gz (a: DCut) : 0 ≤ maximum 0 a := by
  simp_all[le_inst,zero_rw,odown,maximum]

theorem max_sym {a b : DCut} : maximum a b = maximum b a := by
  simp[maximum,Set.union_comm]

@[simp]
theorem max_pos {a : DCut} : 0 ≤ a → maximum 0 a = a := by
  simp[maximum,le_inst,DCut.ext_iff]

@[simp]
theorem max_neg {a : DCut} : a ≤ 0 → maximum 0 a = 0 := by
  simp[maximum,le_inst,DCut.ext_iff]

@[simp]
theorem max_pos_lt {a : DCut} : 0 < a → maximum 0 a = a := by
   simp[maximum,lt_inst,DCut.ext_iff]

@[simp]
theorem max_neg_lt {a : DCut} : a < 0 → maximum 0 a = 0 := by
   simp[maximum,lt_inst,DCut.ext_iff]

@[simp]
theorem max_self {a : DCut} : maximum a a = a := by
   simp[maximum,lt_inst,DCut.ext_iff]

@[simp]
theorem max_pos_to_neg {a: DCut} (ha : 0 < a) : maximum 0 (-a) = 0 := by
  simp[maximum,lt_inst,DCut.ext_iff,neg_inst,neg,preneg,zero_rw,odown]
  intro x y hy z hz hxyz
  have ⟨ q, ⟨ hq1, hq2 ⟩ ⟩ := non_neg_in_pos ha
  have := a_lt_b hq1 hz
  linarith

theorem neg_lt {a : DCut}: 0 < a ↔ -a < 0 := by
  constructor
  . simp_all[lt_inst]
    intro h1 h2
    apply And.intro
    . intro h
      exact h1 (Eq.symm h)
    . intro x ⟨ q, ⟨ hq, ⟨ r, ⟨ hr, hqr ⟩ ⟩ ⟩ ⟩
      have h4 := a_lt_b (h2 hq) hr
      simp[zero_rw,odown]
      linarith
  . intro ⟨ h1, h2 ⟩
    apply And.intro
    . exact id (Ne.symm (neg_ne_zero.mp h1))
    . by_contra h
      have ⟨ z, ⟨ hz1, hz2 ⟩ ⟩ := Set.not_subset.mp h
      simp[neg_inst,neg,preneg,zero_rw,odown] at h2
      have := h2 0 z hz1 z hz2 (by linarith)
      simp at this

theorem neg_le {a : DCut} : 0 ≤ a ↔ -a ≤ 0 := by
  simp[le_of_lt,@neg_lt a,eq_comm]

theorem neg_lt' {a : DCut} : a < 0 ↔ 0 < -a := by

  constructor
  . intro ⟨ h1, h2 ⟩
    apply And.intro
    . simp[DCut.ext_iff] at h1 ⊢
      exact h1
    . intro q hq
      simp[neg_inst,neg,preneg]
      simp[zero_rw,odown] at hq
      have : 0 ∉ a.A := by
        intro h
        have := h2 h
        simp[zero_rw,odown] at this
      exact ⟨ q, ⟨ hq, ⟨ 0, ⟨ this, by linarith ⟩ ⟩ ⟩ ⟩
  . simp[lt_inst]
    intro ha h
    apply And.intro
    . exact ha
    . by_contra hnq
      have ⟨ z, ⟨ hz1, hz2 ⟩ ⟩ := Set.not_subset.mp hnq
      simp[neg_inst,neg,preneg,zero_rw,odown] at h hz2
      have ⟨ s, ⟨ hs1, hs2 ⟩ ⟩ := a.op z hz1
      have ⟨ q, ⟨ hq, ⟨ r, ⟨ hr1, hr2 ⟩ ⟩ ⟩ ⟩ := h (-s) (by linarith)
      have : s < r := by exact a_lt_b hs1 hr1
      linarith

theorem neg_le' {a : DCut} : a ≤ 0 ↔ 0 ≤ -a := by
  simp[le_of_lt,@neg_lt' a,eq_comm]

theorem pos_neg_sum {a : DCut} : a = maximum 0 a - maximum 0 (-a) := by
  by_cases h : 0 < a
  . rw[max_pos h.right]
    rw[max_neg (neg_le.mp h.right)]
    exact Eq.symm (sub_zero a)
  . have := trichotomy_lt 0 a
    simp[not_gt_to_le] at h
    apply Or.elim this
    . intro h'
      rw[max_pos_lt h']
      have := neg_lt.mp h'
      rw[max_neg_lt this]
      simp
    . intro h'
      rw[max_neg h]
      have := neg_le'.mp h
      rw[max_pos this]
      simp

@[simp]
theorem neg_max_zero_neg {a : DCut} (ha : a ≤ 0) : -maximum 0 (-a) = a := by
   have : 0 ≤ -a := by
     rw[neg_le'] at ha
     exact ha
   simp[max_pos,this]
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
