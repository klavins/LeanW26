
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Distributivity.lean'>Code</a> for this chapter</span>
 # The Distributive Property 
```lean
theorem pos_distrib {a b c : DCut} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : mul_pos a (sum b c) ha (sum_pos_pos hb hc) = sum (mul_pos a b ha hb) (mul_pos a c ha hc) := by

  ext q
  constructor

  . intro hq
    choose x hx yz hyz hx0 hyz0 hxyz using hq
    choose y hy z hz hyz using hyz
    rw[←hyz] at hxyz

    have hxy := prod_in_pos_mul ha hb hx hy hx0
    have hxz := prod_in_pos_mul ha hc hx hz hx0

    apply (sum (mul_pos a b ha hb) (mul_pos a c ha hc)).dc q (x*y + x*z)
    split_ands
    . linarith
    . simp[sum,presum]
      exact ⟨ x*y, ⟨ hxy, ⟨ x*z, ⟨ hxz, rfl⟩ ⟩ ⟩ ⟩

  . intro hq
    choose xy hxy xz hxz h using hq
    choose x₁ hx₁ y hy hx₁0 hy0 hx₁y using hxy
    choose x₂ hx₂ z hz hx₂0 hz0 hx₂z using hxz

    let x := max x₁ x₂
    have hx1 : x ∈ a.A := by
      by_cases g : x₁ ≤ x₂
      . have : x = x₂ := by exact max_eq_right g
        exact Set.mem_of_eq_of_mem this hx₂
      . have : x = x₁ := by exact max_eq_left (by linarith)
        exact Set.mem_of_eq_of_mem this hx₁
    have hx2 : 0 < x := by exact lt_sup_of_lt_left hx₁0

    obtain ⟨ x', ⟨ hx1', hx2' ⟩ ⟩ := a.op x hx1

    have : y + z ∈ (sum b c).A := by
      exact ⟨ y, ⟨ hy, ⟨ z, ⟨ hz, rfl ⟩ ⟩ ⟩ ⟩

    have hxyz : x*(y+z) ∈ (mul_pos a (sum b c) ha (sum_pos_pos hb hc)).A := by
      use! x', hx1', y+z, this
      split_ands
      repeat
      nlinarith

    apply (mul_pos a (sum b c) ha (sum_pos_pos hb hc)).dc q (x*(y+z))

    split_ands
    . have h' : q < x₁ * y + x₂ * z := by linarith
      have w1 : x₁ ≤ x := by exact le_max_left x₁ x₂
      have w2 : x₂ ≤ x := by exact le_max_right x₁ x₂
      nlinarith
    . exact hxyz

theorem nneg_distrib {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : mul_nneg a (b + c) ha (sum_nneg_nneg hb hc) =
    (mul_nneg a b ha hb) + (mul_nneg a c ha hc) := by
  rcases three_nn_ineqs ha hb hc with ⟨ ha', hb', hc' ⟩ | h | h | h
  . have h1 := nneg_eq_pos ha' (sum_pos_pos hb' hc')
    have h2 := nneg_eq_pos ha' hb'
    have h3 := nneg_eq_pos ha' hc'
    simp[hadd_inst] at h1
    simp[h1,h2,h3,hadd_inst]
    exact pos_distrib ha' hb' hc'
  repeat
  simp[h]

theorem nn_distrib {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : a * (b + c) = a*b + a*c := by
  simp[hmul_inst,mul]
  simp[ha,hb,hc,neg_le.mp,sum_nneg_nneg]
  have : -c + -b ≤ 0 := by
    have := sum_nneg_nneg hc hb
    rw[negate_le,neg_add_rev,add_comm] at this
    exact this
  simp[this,sum_nneg_nneg,nneg_distrib,ha,hb,hc]

theorem bn_distrib {a b c : DCut} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) :
  a * (b + c) = a * b + a * c := by
  by_cases h : 0 ≤ c+b
  . have h2 : a * ( (c+b) + (-b)) = a*(c+b) + a*(-b) := nn_distrib ha h (flip hb)
    simp at h2
    rw[h2]
    simp[add_comm]
  . apply neg_t.mpr at h
    apply lt_imp_le at h
    rw[←negate_le'] at h
    have h2 : a * ( -(c+b) + c ) = a*(-(c+b)) + a*c := nn_distrib ha h hc
    simp at h2
    apply neg_inj.mpr at h2
    rw[neg_neg] at h2
    rw[h2]
    simp
    rw[←neg_add,mul_neg_dist_left,neg_neg]

theorem distrib {a b c : DCut}
  : a*(b+c) = a*b+a*c := by
  rcases three_ineqs a b c with ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩

  . exact nn_distrib ha hb hc

  . have := nn_distrib (flip ha) hb hc
    rw[Iff.symm neg_inj,add_comm] at this
    simp_all[add_comm]

  . exact bn_distrib ha hb hc

  . have := bn_distrib ha hc hb
    simp[mul_neg_dist_right] at this
    rw[neg_sum_eq]
    rw[add_comm]
    rw[this]
    exact SubtractionMonoid.neg_add_rev (a * c) (a * b)

  . have := bn_distrib (flip ha) hb hc
    simp[mul_neg_dist_right] at this
    rw[neg_sum_eq]
    exact this

  . have := bn_distrib (flip ha) hc hb
    simp[mul_neg_dist_right] at this
    rw[neg_sum_eq]
    rw[add_comm]
    rw[this]
    exact sum_comm

  . have := nn_distrib ha (flip hb) (flip hc)
    simp only [←neg_add, mul_neg_dist_left, mul_neg_dist_right, neg_neg] at this
    rw[Iff.symm neg_inj]
    exact this

  . have := nn_distrib (flip ha) (flip hb) (flip hc)
    simp only [←neg_add, mul_neg_dist_left, mul_neg_dist_right, neg_neg] at this
    exact this

theorem distrib_right {a b c : DCut}
  : (a+b)*c = a*c+b*c := by
  have := @distrib c a b
  rw [mul_comm] at this
  simp[this,mul_comm,add_comm]
```
 ## Cuts Form a Commutative Ring 
```lean
instance nunasr_inst :  NonUnitalNonAssocSemiring DCut := ⟨
  @distrib,
  @distrib_right,
  @mul_zero_left,
  @mul_zero_right
⟩

instance nusr_inst : NonUnitalSemiring DCut := ⟨
  λ x y z => Eq.symm (@mul_assoc x y z)
⟩

instance semi_ring_inst : Semiring DCut := ⟨
  @mul_id_left,
  @mul_id_right,
  rfl,
  Nat.cast_add_one,
  npow,
  @npow_zero,
  @npow_succ
⟩

def smul (z : ℤ) (a : DCut) : DCut := (ofRat z) * a

theorem smul_zero_left {a : DCut} : smul 0 a = 0 := by
  have : ofRat 0 = 0 := rfl
  simp[smul,this,mul_zero_left]

theorem smul_succ {n : ℕ} {a : DCut}
  : smul (↑n.succ) a = smul (↑n) a + a := by
  simp[smul,add_rats,mul_comm,distrib]
  have : ofRat 1 = 1 := rfl
  simp[this]

theorem smul_neg_succ {n : ℕ} {a : DCut}
  : smul (Int.negSucc n) a = -smul (↑n.succ) a := by
  simp[smul,add_rats,mul_comm,distrib]
  simp[←neg_of_rat]

theorem int_cast_neg_succ (n : ℕ) :
    int_cast_inst.intCast (Int.negSucc n) = -↑(n + 1) := by
    simp[IntCast.intCast,Int.negSucc,add_rats,neg_inst]
    simp[←neg_of_rat]
    have : -ofRat 1 = -1 := rfl
    simp[this]
    rfl

instance ring_inst : Ring DCut := ⟨
  add_neg,
  smul,
  @smul_zero_left,
  @smul_succ,
  @smul_neg_succ,
  @neg_add_cancel_left,
  λ _ => rfl,
  int_cast_neg_succ
⟩

instance com_ring_inst : CommRing DCut := ⟨
  @mul_comm
⟩
```
 With `CommRing` instantiated, we should be able to use the `ring` tactic on cuts. 
```lean
example {a b c : DCut} : a*(b+c) - c = a*c - c + a*b := by
  ring

example {a b : DCut} : (a-b)^2 = a^2 - 2*a*b + b^2 := by
  ring
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
