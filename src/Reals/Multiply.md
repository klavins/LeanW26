
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Multiply.lean'>Code</a> for this chapter</span>
 # Multiplication

Multiplication of Dedekind cuts is straightfoward, but also fairly involved, or as Rudin says: "bothersome". The issue is dealing with both positive and negative cuts. Following Rudin, the development of the definitions proceeds as follows:

- Define multiplication on positive cuts.
- Extend multiplciation on positive cuts to non-negative cuts, building on the previous step by handling the cases in which either or both of the cuts is zero.
- Extend multiplication on non-negative cuts to all cuts.

For each of the above definitions of multiplication, we also prove the properties required to show that multiplication forms a commutiative group on cuts:
- 0 is an identity: `0*x = 0`
- Multiplication is commutative: `x*y = y*x`
- Associativity: `x*(y*z) = (x*y)*z`
The last property is particularly challenging, because to relate arbitary reals with positive reals, one has to deal with an abundance of cases, preferably gracefully. Thus, along the way we will prove several intermediate results which allow us to make the proof more concise. 
 ## Definitions

### Multiplication of Positive Cuts

Given two positive cuts `0 < a` and `0 < b`, their product is the set of points `z` such that for some `x ∈ a` and `y ∈ b`, `z < x*y`. This basic definition underlies the entire framework for multiplication, after which we simply have to deal with various combinations of non-negative and negative numbers. 
```lean
def pre_mul (a b : DCut) :=
  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, 0 < x ∧ 0 < y ∧ z < x*y }
```
 To make some proofs more readable, it is useful to characterize pre_mul the following sufficient condition. 
```lean
theorem pre_mul_suffice {a b : DCut} {x y z : ℚ}
  : x ∈ a.A → y ∈ b.A → 0 < x → 0 < y → z < x*y → z ∈ pre_mul a b := by
  intro hx hy _ _ _
  use x, hx, y, hy
```
 To prove that this definition results in a cut, we need to prove as usual that it is non-empty, not equal to ℚ, downward closed, and open.

First, we show `pre_mul a b` is non-empty, by showing that it contains `0`. Since `a` and `b` are positive, they contain `0`. By the `op` property, `a` and `b` must also contain values `x` and `y` larger than zero. Then 0 < x*y as well, satisfying the definition. 
```lean
theorem pre_mul_ne {a b : DCut} (ha : 0 < a) (hb : 0 < b) : ∃ q, q ∈ pre_mul a b := by

  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ : ∃ x ∈ a.A, 0 < x := a.op 0 (zero_in_pos ha)
  have ⟨ y, ⟨ hy1, hy2 ⟩ ⟩ : ∃ y ∈ b.A, 0 < y := b.op 0 (zero_in_pos hb)
  use 0
  apply pre_mul_suffice hx1 hy1 hx2 hy2
  nlinarith
```
  To show `pre_mul a b` is not `ℚ`, we choose `x` and `y` not in `a` and `b` respectively and show that `x*y`is bigger than every value in in `pre_mul a b`. Although this proof does not require that `a` and `b` are positive, we include these conditions anyway for consistency. 
```lean
theorem pre_mul_nf {a b : DCut} (_ : 0 < a) (_ : 0 < b)
  : ∃ q, q ∉ pre_mul a b := by
  obtain ⟨ x, ⟨ hx, hx' ⟩ ⟩ := has_ub a
  obtain ⟨ y, ⟨ hy, hy' ⟩ ⟩ := has_ub b
  use x*y
  apply ub_to_notin
  intro q hq
  choose s hs t ht hs0 ht0 hqst using hq
  nlinarith[hx' s hs, hy' t ht]
```
 That `pre_mul a b` is downward closed is results from a straightforward unpacking of the definitions. 
```lean
theorem pre_mul_dc {a b : DCut}
  : ∀ x y, x ≤ y ∧ y ∈ (pre_mul a b) → x ∈ (pre_mul a b) := by
  intro x y ⟨ hxy, hy ⟩
  obtain ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, ⟨ hsp, ⟨ htp, hyst ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ := hy
  exact pre_mul_suffice hs ht hsp htp (lt_of_le_of_lt hxy hyst)
```
 To show `pre_mul a b` is open, we start with values `s` and `t` in `a` and `b` respectively. Since `a` and `b` are open, we obtain values `s'` and `t'` in that are greater that `s` and `t` and still in `a` and `b`. Then `s*t < s'*t'` as required. 
```lean
theorem pre_mul_op {a b : DCut}
  : ∀ x ∈ (pre_mul a b), ∃ y ∈ (pre_mul a b), x < y := by
  intro x ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, ⟨ hsp, ⟨ htp, hyst ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  have ⟨ s', ⟨ hs', hss' ⟩ ⟩ := a.op s hs
  have ⟨ t', ⟨ ht', htt' ⟩ ⟩ := b.op t ht
  have h: s*t < s'*t' := by nlinarith
  use! s*t, s', hs', t', ht'
  split_ands
  repeat
  linarith
```
 Grouping these properties together we have a proof that this definition of multiplication results in a proper cut. 
```lean
def mul_pos (a b : DCut) (ha : 0 < a) (hb : 0 < b) : DCut :=
  ⟨ pre_mul a b, pre_mul_ne ha hb, pre_mul_nf ha hb, pre_mul_dc, pre_mul_op ⟩
```
 We will need the following property to extend multiplication from positive numbers to non-negative numbers stating that the product of two positive numbers is again positive. Thus, the definition `pre_mul` operates exclusively on the positive reals. 
```lean
theorem zero_in_pre_mul  {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : 0 ∈ pre_mul a b  := by
  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := non_neg_in_pos ha
  have ⟨ y, ⟨ hy1, hy2 ⟩ ⟩ := non_neg_in_pos hb
  use! x, hx1, y, hy1, hx2, hy2
  nlinarith

theorem mul_is_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : 0 < mul_pos a b ha hb := by
  apply pos_has_zero.mpr
  exact zero_in_pre_mul ha hb
```
 ### Multiplication on Non-negative Cuts

We now extend the definition to non-negative reals, essentially dealing with the cases in which either cut is zero, in which case the resulting product is zero. Indeed, if one of `a` and `b` is zero, then `pre_mul a b = ∅`. 
```lean
example {A : Set ℕ}: A ⊆ ∅ ↔ A = ∅ := by exact Set.subset_empty_iff

@[simp]
theorem zero_mul_empty {a b : DCut} (h : 0 = a ∨ 0 = b) : pre_mul a b = ∅ := by
  rcases h with h | h
  repeat
  . simp[pre_mul,←h,zero_rw,odown]
    ext
    simp
    intros
    linarith
```
 Since `∅` is not a valid cut, we use `pre_mul a b ∪ odown 0` to represent the product of two non-negative cuts. Of course, if `a` and `b` are positive cuts, then `pre_mul a b` is downward closed, so the union with `odown 0` is not needed. 
```lean
@[simp]
theorem non_zero_mul_subsume {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : pre_mul a b ∪ odown 0 = pre_mul a b := by
  simp_all[lt_inst]
  exact lt_imp_le (mul_is_pos ha hb)
```
 The usual theorems are required to show that the product is a cut. We simply have to deal with the possible cases. 
```lean
theorem mul_nneg_ne {a b : DCut}
  : ∃ q, q ∈ pre_mul a b ∪ odown 0 := by
  use -1
  apply Or.inr
  simp[odown]

theorem mul_nneg_nf {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : ∃ q, q ∉ pre_mul a b ∪ odown 0 := by
  rcases two_nn_ineqs ha hb with ⟨ ha, hb ⟩ | h | h
  . simp[pre_mul_nf,ha,hb]
  repeat
  . simp[h,odown]
    exact ⟨ 1, rfl ⟩

theorem mul_nneg_dc {a b : DCut} {x y : ℚ}
  : x ≤ y ∧ y ∈ pre_mul a b ∪ odown 0 → x ∈ pre_mul a b ∪ odown 0 := by
  intro ⟨ h1, h2 ⟩
  apply Or.elim h2
  . intro hy
    apply Or.inl
    exact pre_mul_dc x y ⟨ h1, hy ⟩
  . intro hy
    apply Or.inr
    exact odown_dc x y ⟨ h1, hy ⟩

theorem mul_nneg_op {a b : DCut} (x : ℚ) :
  x ∈ pre_mul a b ∪ odown 0 → ∃ y ∈ pre_mul a b ∪ odown 0, x < y := by
  intro h
  apply Or.elim h
  . intro hx
    have ⟨ q, ⟨ hq1, hq2 ⟩ ⟩ := pre_mul_op x hx
    use q
    exact ⟨ Or.inl hq1, hq2 ⟩
  . intro hx
    use x/2
    simp_all[odown]
    exact ⟨ Or.inr (by linarith), by linarith ⟩

def mul_nneg (a b : DCut) (ha : 0 ≤ a) (hb : 0 ≤ b) : DCut :=
  ⟨ pre_mul a b ∪ odown 0,
    mul_nneg_ne,
    mul_nneg_nf ha hb,
    @mul_nneg_dc a b,
    @mul_nneg_op a b ⟩
```
 We note that when `a` and `b` are positive cuts, that `mul_nneg` agrees with `mul_pos`. 
```lean
theorem nneg_eq_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : mul_nneg a b (lt_imp_le ha) (lt_imp_le hb) = mul_pos a b ha hb := by
  simp_all[mul_is_pos,ha,hb,mul_nneg,mul_pos]
```
 ### Mulitiplication on Arbitrary Cuts

Finally, we extend multiiplcation to arbitrary cuts. This step uses the fact that every cut `a` can be written as the difference `max 0 a - max 0 (-a)`. If `0 ≤ a` then
```hs
max 0 a - max 0 (-a) = a + 0
```
and if `a < 0` then
```hs
max 0 a - max 0 (-a) = 0 + -a
```
both of which are non-negative, and we can therefore use the previous definition of multiplication on non-negative cuts.

```lean
def mul (a b : DCut) : DCut :=
  let ap := maximum 0 a
  let an := maximum 0 (-a)
  let bp := maximum 0 b
  let bn := maximum 0 (-b)
  (mul_nneg ap bp (max_gz _) (max_gz _)) +
  (mul_nneg an bn (max_gz _) (max_gz _)) -
  (mul_nneg ap bn (max_gz _) (max_gz _)) -
  (mul_nneg an bp (max_gz _) (max_gz _))
```
 We may now instantiate the notation classes for multiplcation. 
```lean
instance hmul_inst : HMul DCut DCut DCut := ⟨ mul ⟩
instance mul_inst : Mul DCut := ⟨ mul ⟩

example : (1:DCut) * 0 = 0 := by
  simp[hmul_inst,mul]
```
 ## Multiplication by 0

For non-negative cuts, it is useful to know that `0*a = 0` and `a*0 = 0`, as these properties allow us to reason about the zero cases in the non-negative commutativity proof. These properties also allow us to show that `0` is the multiplicative identity, which is needed for proving cuts with multiplication form a group. 
```lean
@[simp]
theorem mul_nneg_zero_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 0 a (λ _ a => a) ha = 0 := by
  simp[mul_nneg,DCut.ext_iff,zero_rw]

@[simp]
theorem mul_nneg_zero_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 0 ha (λ _ a => a) = 0 := by
  simp[mul_nneg,DCut.ext_iff,zero_rw]
```
 These two theorems allow us to prove that the multiple of two non-negative cuts is again non-negative. 
```lean
@[simp]
theorem mul_is_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : 0 ≤ mul_nneg a b ha hb := by
  rcases two_nn_ineqs ha hb with ⟨ ha, hb ⟩ | h | h
  . rw[nneg_eq_pos ha hb]
    exact lt_imp_le (mul_is_pos ha hb)
  repeat
  . simp[←h]
    simp_all[lt_of_le]
```
 We can extend these properties to arbitrary cuts. 
```lean
@[simp]
theorem mul_zero_left {a : DCut} : 0 * a = 0 := by
  simp[hmul_inst,mul]

@[simp]
theorem mul_zero_right {a : DCut} : a * 0 = 0 := by
  simp[hmul_inst,mul]

instance mul_zero_inst : MulZeroClass DCut := ⟨
    @mul_zero_left,
    @mul_zero_right
  ⟩
```
 ## Commutativity

For positive cuts, commutativity is straightfoward, as it simply amounts to reordering x and y in the definition of `pre_mul`. 
```lean
theorem mul_pos_comm {a b : DCut} (ha : 0 < a) (hb : 0 < b)
  : mul_pos a b ha hb = mul_pos b a hb ha  := by
  ext q
  constructor
  repeat
  . intro ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ h1, ⟨ h2, h3 ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    exact ⟨ y, ⟨ hy, ⟨ x, ⟨ hx, ⟨ h2, ⟨ h1, by linarith ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
```
 Proving commutativity for non-negative cuts amounts to three cases, where `a` and `b` are both positive and where one or the other is negative. 
```lean
theorem mul_nneg_comm {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : mul_nneg a b ha hb = mul_nneg b a hb ha := by

  rcases two_nn_ineqs ha hb with ⟨ ha, hb ⟩ | h | h
  . simp[mul_nneg]
    have := mul_pos_comm ha hb
    simp_all[mul_pos]
  repeat
  . simp[h]
```
 The proof of commutativity for arbitrary cuts requires us to reason about every possible combination of non-negative and negative cuts. We do this with the theorem `two_ineqs_true` which enuerates all four cases. For each case, the same simplificiation works. 
```lean
theorem mul_comm {a b : DCut}: a*b = b*a := by
  rcases two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat
  simp[ha,hb,hmul_inst,mul,mul_nneg_comm,neg_le.mp]
```
 ## Multiplication by 1

The proof that `1*x=x` is split into three main steps for positive, non-negative, and arbitary cuts. For positive cuts, the proof is split into two parts that show `1*a ≤ a` and `a*1 ≤ 1` respectively. The first direction is straightforward, and uses the fact that `a` is downward closed.


```lean
theorem mul_pos_id_left_1 {a : DCut} (ha: 0 < a)
  : mul_pos 1 a zero_lt_one ha ≤ a := by
  intro q ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, ⟨ hx0, ⟨ hy0, hqxy ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  apply a.dc q (x*y)
  split_ands
  . linarith
  . have hxy : x*y < y := mul_lt_of_lt_one_left hy0 hx
    exact a.dc (x*y) y ⟨ by linarith, hy ⟩
```
 For the other direction, we assume we have `q ∈ a.A` and need to show `q` is in `mul_pos 1 a`. This is done differently depending on whether `q` is positive or non-negative. For the first case, we use the fact that `a.A` is open to find `s` and `t` in `a.A` with `q < s < t`. Then `q < s*t` as required. For `q` non-negative, we use the fact that `0 ∈ a.A` and find `s ∈ a.A` with `0<s`. We also have `1/2 ∈ odown 1`. Then `q < s*(1/2)` as required.

```lean
theorem mul_pos_id_left_2 {a : DCut} (ha: 0 < a)
  : a ≤ mul_pos 1 a zero_lt_one ha := by
  intro q hq
  simp[mul_pos]
  by_cases h : 0 < q
  . have ⟨ s, ⟨ t, ⟨ hx, ⟨ ht1, ⟨ hsq, st ⟩ ⟩ ⟩ ⟩ ⟩ := op2 q hq
    have hs3 : 0 < s := by linarith
    refine pre_mul_suffice ?_ ht1 (div_pos h hs3) ?_ ?_
    . apply in_one
      exact Bound.div_lt_one_of_pos_of_lt hs3 (by linarith)
    . linarith
    . have hts : t/s > 1 := (one_lt_div hs3).mpr (by linarith)
      have hqts : q*(t/s) = q / s * t := Eq.symm (mul_comm_div q s t)
      nlinarith
  . have ⟨s, ⟨ hs1, hs2 ⟩ ⟩ := a.op 0 (zero_in_pos ha)
    refine pre_mul_suffice ?_ hs1 one_half_pos hs2 ?_
    . apply in_one
      linarith
    . linarith
```
 Combining the above inequalities gives the main result for positive cuts. 
```lean
@[simp]
theorem mul_pos_id_left {a : DCut} (ha: 0 < a)
  : mul_pos 1 a zero_lt_one ha = a := by
  apply PartialOrder.le_antisymm
  . exact mul_pos_id_left_1 ha
  . exact mul_pos_id_left_2 ha
```
 For non-negative cuts, we consider the cases where `0 = a` and `0 < a` separately. 
```lean
@[simp]
theorem mul_nneg_id_left {a : DCut} (ha: 0 ≤ a)
  : mul_nneg 1 a zero_le_one ha = a := by
    rw[le_of_lt] at ha
    rcases ha with h1 | h2
    . simp[←h1]
    . have := mul_pos_id_left h2
      simp_all[mul_pos,DCut.ext_iff,mul_nneg,DCut.ext_iff]
      exact ha
```
 Commutativity makes it easy to prove similar versions of theorems for which one side has already been established. For example: 
```lean
@[simp]
theorem mul_nneg_id_right {a : DCut} (ha: 0 ≤ a)
  : mul_nneg a 1 ha zero_le_one = a := by
  rw[mul_nneg_comm,mul_nneg_id_left]
```
 And similarly, 
```lean
@[simp]
theorem mul_id_right {a : DCut} : a * 1 = a := by
  simp only[hmul_inst,mul]
  by_cases ha : 0 < a
  . simp[ha]
  . simp
    rw[not_gt_to_le] at ha
    simp[ha]

@[simp]
theorem mul_id_left {a : DCut} : 1 * a = a := by
  simp[mul_comm]
```
 Mathlib includes a class that keeps track of these properties. 
```lean
instance mul_one_inst : MulOneClass DCut := ⟨
  @mul_id_left,
  @mul_id_right
⟩
```
 ## Associativity

The proof that `mul` is associatve amounts to a lot of book-keeping around some simple observations. We start with a proof that `mul_pos` is associatve, which has two directions to prove. Each uses the fact that the cuts are open.   
```lean
theorem mul_pos_assoc {a b c : DCut} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  : mul_pos a (mul_pos b c hb hc) ha (mul_is_pos hb hc) =
    mul_pos (mul_pos a b ha hb) c (mul_is_pos ha hb) hc  := by

  ext q
  constructor

  . choose x hx yz h' hx0 hyz0 hq
    choose y hy z hz hy0 hz0 hyz' using h'
    obtain ⟨ x', ⟨ hx', hxx' ⟩ ⟩ : ∃ x' ∈ a.A, x < x' := a.op x hx
    use x*y
    constructor
    . use! x', hx', y
      simp_all
      nlinarith
    . use z
      simp_all
      nlinarith

  . choose xy h' z hz hxy hx0 hq
    choose x hx y hy hz0 hy0 hxy' using h'
    have ⟨ z', ⟨ hz', hzz' ⟩ ⟩ : ∃ z' ∈ c.A, z <z' := c.op z hz
    use! x, hx, y*z
    constructor
    . use y, hy, z'
      simp_all
      nlinarith
    . simp_all
      nlinarith
```
 Extending this result to non-negative cuts requires reasoning about four cases, convenienly available through the `three_nn_ineqs` theorem. 
```lean
@[simp]
theorem mul_nneg_assoc {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : mul_nneg a (mul_nneg b c hb hc) ha (mul_is_nneg hb hc) =
    mul_nneg (mul_nneg a b ha hb) c (mul_is_nneg ha hb) hc := by

  rcases three_nn_ineqs ha hb hc with ⟨ ha', hb', hc' ⟩ | h | h | h

  . simp[mul_nneg]
    congr -- removes `∪ odown 0`
    simpa[mul_pos,ha',hb',hc'] using mul_pos_assoc ha' hb' hc'

  repeat
  . simp[h]
```


To prove associativity in general, it is tempting to look at 27 possible cases in which each of three cuts are positive, zero or negative. However, we can take advantage of some basic algebra to reduce the number of cases to eight. To proceed, note that when `a ≤ 0` while `0 ≤ b` and `0 ≤ c`, then
```hs
(a*b)*c = a*(b*c)
```
becomes
```hs
-((-a)*b)*c = -((-a)*(b*c))
```
and then use mul_assoc_all_nn. Similarly, we can do all the other cases this way.

```lean
@[simp]
theorem mul_neg_dist_left {a b : DCut} : a*(-b) = -(a*b) := by
  simp[hmul_inst,mul]
  rcases two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat
  simp[ha,hb,neg_le.mp]

@[simp]
theorem mul_neg_dist_right {a b : DCut} : (-a)*b = -(a*b) := by
  simp only[hmul_inst,mul]
  rcases two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
  repeat
  simp[ha,hb,neg_le.mp]
```
 To make the proof more readable, we rewrite the theorem for non-negative cuts in terms of arbitrary cuts. 
```lean
theorem mul_assoc_all_nn {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : a * (b * c) = (a * b) * c := by
  simp[hmul_inst,mul]
  simp[ha,hb,hc,neg_le.mp] -- uses mul_nneg_assoc
```
 And we prove a simple theorem that allows us to flip the direction of an inequality involving a negative cut. 
```lean
theorem flip {a : DCut} (ha: a < 0) : 0 ≤ -a := neg_le'.mp (lt_imp_le ha)
```
 Finally, combining the above, we can use the simplifier, `flip` and  `mul_assoc_all_nn` to prove associativity for arbitrary cuts. 
```lean
theorem mul_assoc {a b c : DCut} : a * (b * c) = (a * b) * c := by
  rcases three_ineqs a b c with ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩ |
                                ⟨ ha, hb, hc ⟩ | ⟨ ha, hb, hc ⟩
  . exact mul_assoc_all_nn ha hb hc
  . simpa using mul_assoc_all_nn (flip ha) hb hc
  . simpa using mul_assoc_all_nn ha (flip hb) hc
  . simpa using mul_assoc_all_nn ha hb (flip hc)
  . simpa using mul_assoc_all_nn (flip ha) (flip hb) hc
  . simpa using mul_assoc_all_nn (flip ha) hb (flip hc)
  . simpa using mul_assoc_all_nn ha (flip hb) (flip hc)
  . simpa using mul_assoc_all_nn (flip ha) (flip hb) (flip hc)
```
 ## Instantiating Multiplication Classes

With associatively and commutivity proved, we can show that multiplication forms a semigroup and a commutative magma. 
```lean
instance semigroup_inst : Semigroup DCut := ⟨
  λ x y z => Eq.symm (@mul_assoc x y z)
⟩

instance semigroup_w_zero_inst : SemigroupWithZero DCut := ⟨
  @mul_zero_left,
  @mul_zero_right
⟩

instance mul_zo_inst : MulZeroOneClass DCut := ⟨
  @mul_zero_left,
  @mul_zero_right
⟩

instance comm_magma_inst : CommMagma DCut := ⟨ @mul_comm ⟩

instance comm_semigroup_inst : CommSemigroup DCut := ⟨ @mul_comm ⟩
```
 ## Natural Powers and Monoid Instance

Mathlib's class structure that leads to instantiating a type as a field includes showing the type is a Monoid, which includes a method for raising a cut `x` to a natural numbered power, as in `x^n`. We define that method here.

```lean
def npow (n: ℕ) (x : DCut) : DCut := match n with
  | Nat.zero => 1
  | Nat.succ k => x * (npow k x)
```
 And show to obvious statements about such powers. 
```lean
theorem npow_zero {x : DCut} : npow 0 x = 1 := by rfl

theorem npow_succ {n : ℕ} {x : DCut} : npow (n+1) x = npow n x * x := by
  simp[npow,mul_comm]
```
 Together these properties allow us to instante DCut as a Monoid, a Commutative Monoind, and a Commutative Monoid with zero. 
```lean
instance monoid_inst : Monoid DCut := ⟨
  @mul_id_left,
  @mul_id_right, -- why does this need to be here if this is already a MulOneClass?
  npow,
  @npow_zero,
  @npow_succ
⟩

instance com_monoid_inst : CommMonoid DCut := ⟨
  @mul_comm
⟩

instance monoid_wz_inst : MonoidWithZero DCut := ⟨
  @mul_zero_left,
  @mul_zero_right
⟩

instance comm_monoid_wz_inst : CommMonoidWithZero DCut := ⟨
  @mul_zero_left,
  @mul_zero_right
⟩
```
 Here is a simple example that use a theorem about monoids from Mathlib. 
```lean
example (x : DCut) : x^2 = x*x := by
  exact pow_two x
```
 # Properties 
```lean
theorem prod_in_pos_mul {a b : DCut} {x y: ℚ} (ha : 0 < a) (hb : 0 < b)
                        (hx : x ∈ a.A) (hy : y ∈ b.A) (hx0 : 0 < x)
  : x*y ∈ (mul_pos a b ha hb).A := by
  obtain ⟨ x', ⟨ hx1', hx2' ⟩ ⟩ := a.op x hx
  obtain ⟨ y', ⟨ hy1', hy2' ⟩ ⟩ := op_from_two_vals hy (zero_in_pos hb)
  have hy' : 0 ≤ y' := by  linarith
  have hxy' : x * y < x' * y' := by
    have h1 : 0 < x' := by linarith
    have h2 : y ≤ y' := by linarith
    nlinarith
  exact ⟨ x', ⟨ hx1', ⟨ y', ⟨ hy1', ⟨ by linarith, ⟨ by linarith, hxy' ⟩ ⟩  ⟩ ⟩ ⟩ ⟩
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
