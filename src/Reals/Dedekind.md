
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Dedekind.lean'>Code</a> for this chapter</span>
 # The Dedekind Reals

Dedekind's representation of a real number `r` is as a pair `(A,B)` where `A ⊆ ℚ` is the set of all rational numbers less than `r` and `B = ℚ \ A`. The idea is that `A` approximates `r` from below and `B` approximates `r` from above. In the case that `r ∈ ℚ`, then `A = (∞,r)` and `B = [r,∞)`. Since `A` completely determines the cut, we work mainly with it, only occasionally referring to `B`.

That this definition satisfies the properties of the real numbers needs to be proved, which is what this chapter is about. Specifically, we will prove that

  - The set of cuts is totally ordered
  - The set of cuts form a _field_
  - Every bounded, non-empty set of cuts has a least upper bound

The last property distinguishes the real numbers from the rationals.

A standard reference for Dedekind cuts is Rudin's Principles of Mathematics. In the 3rd edition, cuts are defined on pages 17-21.

## Definition

First, we define a structure to capture the precise definition of a cut `A ⊆ ℚ`. We require that A is nonempty, that it is not ℚ, that it is downward closed, and that is an open interval. 
```lean
@[ext]
structure DCut where
  A : Set ℚ
  ne : ∃ q, q ∈ A                   -- not empty
  nf : ∃ q, q ∉ A                   -- not ℚ
  dc : ∀ x y, x ≤ y ∧ y ∈ A → x ∈ A -- downward closed
  op : ∀ x ∈ A, ∃ y ∈ A, x < y      -- open

open DCut
```
 We have only defined the lower part, `A` of a cut. The upper part of the cut, `B` is defined simply: 
```lean
def DCut.B (c : DCut) : Set ℚ := Set.univ \ c.A
```
 ## Making Rationals into Reals

All rational numbers are also real numbers via the map that identifies a rational `q` with the interval `(∞,q)` of all rationals less than `q`. We call this set `odown q`, where `odown` is meant to abbreviate `open, downward closed`. 
```lean
def odown (q : ℚ) : Set ℚ := { y | y < q }
```
 To prove that `odown q` is a Dedekind cut requires we show it is nonempty, not `ℚ` itself, downward closed, and open. We will need to do this sort of proof over and over in this section, as we show various other ways of constructing sets of rationals are indeed Dedekind cuts.

For the first two theorems we use use the facts that `q-1 ∈ (∞,q)` and `q+1 ∉ (∞,q)`. 
```lean
theorem odown_ne {q : ℚ} : ∃ x, x ∈ odown q := by
  use q-1
  simp[odown]

theorem odown_nf {q : ℚ} : ∃ x, x ∉ odown q := by
  use q+1
  simp[odown]
```
 That `odown` q is downward closed follows from the definitions. 
```lean
theorem odown_dc {q : ℚ} : ∀ x y, x ≤ y ∧ y ∈ odown q → x ∈ odown q := by
  intro x y ⟨ hx, hy ⟩
  simp_all[odown]
  linarith
```
 To prove `odown q` is open, we are given `x ∈ odown` and need to supply `y ∈ odown q` with `x < y`. Since `q` is the least upper bound of `odown q`, we choose `(x+q)/2`, which is less than `q` and greater than `x`. 
```lean
theorem odown_op {q : ℚ} : ∀ x ∈ odown q, ∃ y ∈ odown q, x < y:= by
  intro x hx
  use (x+q)/2
  simp_all[odown]
  apply And.intro
  repeat linarith
```
 With these theorems we define the map `ofRat : ℚ → DCut` that embeds the rationals into the Dedekind cuts. 
```lean
def ofRat (q : ℚ) : DCut :=
  ⟨ odown q, odown_ne, odown_nf, odown_dc, odown_op ⟩

instance rat_cast_inst : RatCast DCut := ⟨ λ x => ofRat x ⟩

instance nat_cast_inst : NatCast DCut := ⟨ λ x => ofRat x ⟩

instance int_cast_inst : IntCast DCut := ⟨ λ x => ofRat x ⟩
```
 With this map we can define 0 and 1, as well as a couple of helper theorems we will later. 
```lean
instance zero_inst : Zero DCut := ⟨ ofRat 0 ⟩
instance one_inst : One DCut := ⟨ ofRat 1 ⟩
instance inhabited_inst : Inhabited DCut := ⟨ 0 ⟩

theorem zero_rw : A 0 = odown 0 := by rfl
theorem one_rw : A 1 = odown 1 := by rfl

theorem zero_ne_one : (0:DCut) ≠ 1 := by
  intro h
  simp[DCut.ext_iff,zero_rw,one_rw,odown,Set.ext_iff] at h
  have h0 := h (1/2)
  have h1 : (1:ℚ)/2 < 1 := by linarith
  have h2 : ¬(1:ℚ)/2 < 0 := by linarith
  exact h2 (h0.mpr h1)

instance non_triv_inst : Nontrivial DCut := ⟨ ⟨ 0, 1, zero_ne_one ⟩ ⟩
```
 ## Simple Properties of Cuts

Next we define a few basic properties that will be used in later proofs, but that are also good exercises here.

First, if `q` is not in `A` then `q` is in `B`, and vice verse, which together imply that `A` and `B` are a partition of `ℚ`.  
```lean
theorem not_in_a_in_b {c :DCut} {q : ℚ} : q ∉ c.A → q ∈ c.B := by
  simp[B]

theorem not_in_b_in_a {c :DCut} {q : ℚ} : q ∉ c.B → q ∈ c.A := by
  simp[B]
```
 We also have two simple properties describing `A` as a downward closed set. The first simply uses the ordering property of `ℚ`, while the second follows from the fact that `A` is downward closed. 
```lean
theorem ub_to_notin {y:ℚ} {A : Set ℚ}
  : (∀ x ∈ A, x < y) → y ∉ A := by
  intro h hy
  have := h y hy
  simp_all

theorem notin_to_ub {y:ℚ} {a : DCut}
  : y ∉ a.A → (∀ x ∈ a.A, x < y)  := by
  intro hy x hx
  by_contra h
  have := a.dc y x ⟨ by linarith, hx ⟩
  exact hy this
```
 The fact that `A` is open can be used to show a few simple properties as well. Since `A` is open, you can find an element in `A` bigger than any given element in `A`. Thus, you can find two values in `A` bigger than any given element. In fact, you can find an arbitary number of elements in `A` bigger than a given element (see exercises).  
```lean
theorem op2 {a : DCut} (q : ℚ) (hq : q ∈ a.A)
  : ∃ x, ∃ y, x ∈ a.A ∧ y ∈ a.A ∧ q < x ∧ x < y := by
  have ⟨s, ⟨ hs1, hs2 ⟩ ⟩ := a.op q hq
  have ⟨t, ⟨ ht1, ht2 ⟩ ⟩ := a.op s hs1
  use s, t
```
 The following is a simple helper theorem that uses the fact that cuts are open. It is used to simplify a proof in the multiplication section. 
```lean
theorem op_from_two_vals {a : DCut} {x y : ℚ} (hx : x ∈ a.A) (hy : y ∈ a.A)
  : ∃ z ∈ a.A, x < z ∧ y < z := by
  by_cases h : x < y
  . have ⟨ z, ⟨ hz1, hz2 ⟩ ⟩ := a.op y hy
    exact ⟨ z, ⟨ hz1, ⟨ by linarith, hz2 ⟩ ⟩ ⟩
  . have ⟨ z, ⟨ hz1, hz2 ⟩ ⟩ := a.op x hx
    exact ⟨ z, ⟨ hz1, ⟨ hz2, by linarith ⟩ ⟩ ⟩
```
 Next, we show  `x in A` and `y in B`, that `x < y`. 
```lean
theorem b_gt_a {c : DCut} {x y : ℚ} : x ∈ c.A → y ∈ c.B → x < y := by
  intro hx hy
  simp[B] at hy
  by_contra h
  exact  hy (c.dc y x ⟨ Rat.not_lt.mp h, hx ⟩)
```
 An alternative for of this same theorem, in which `B` is characterized as `ℚ \ A` is also useful. 
```lean
theorem a_lt_b {c : DCut} {x y : ℚ }: x ∈ c.A → y ∉ c.A → x < y := by
  intro hx hy
  exact b_gt_a hx (not_in_a_in_b hy)
```
 Next we show that since `A` is downward closed, one can easily show `B` is upward closed. 
```lean
theorem b_up_closed {c : DCut} {a b: ℚ} : a ∉ c.A → a ≤ b → b ∉ c.A := by
  intro h1 h2 h3
  exact h1 (c.dc a b ⟨ h2, h3 ⟩)
```
 ## Ordering

Next we show that cuts are totally ordered by the subset relation. First, we define and instantiate the less than and less than or equal relations on cuts. 
```lean
instance lt_inst : LT DCut := ⟨ λ x y => x ≠ y ∧ x.A ⊆ y.A ⟩
instance le_inst : LE DCut := ⟨ λ x y => x.A ⊆ y.A ⟩
```
 To check these definitions make sense, we verify them with rational numbers. 
```lean
example {x y : ℚ} : x ≤ y → (ofRat x) ≤ (ofRat y) := by
  intro h q hq
  exact gt_of_ge_of_gt h hq
```
 It is useful to be able to rewrite the less than relation `<` in terms of inequality and `≤`, and to rewrite `≤` in terms of equality and `<`.  
```lean
theorem DCut.lt_of_le {x y: DCut} : x < y ↔ x ≠ y ∧ x ≤ y := by
  exact Eq.to_iff rfl

theorem DCut.le_of_lt {x y: DCut} : x ≤ y ↔ x = y ∨ x < y := by
  simp_all[le_inst,lt_inst]
  constructor
  . intro h
    simp[h]
    exact Classical.em (x=y)
  . intro h
    cases h with
    | inl h1 => exact Eq.subset (congrArg A h1)
    | inr h1 => exact h1.right
```
 We can easily prove that cuts form a partial order, which allows us to regiester `DCut` with Mathlib's PartialOrder class. <span style='background: yellow'>TODO: Can't you just used the fact that `⊆` is a partial order?</span> 
```lean
theorem refl {a: DCut} : a ≤ a := by
  simp_all[le_inst,lt_inst]

theorem anti_symm {a b: DCut} : a ≤ b → b ≤ a → a = b := by
  intro hab hba
  ext q
  constructor
  . intro hq
    exact hab (hba (hab hq))
  . intro hq
    exact hba (hab (hba hq))

theorem trans {a b c: DCut} : a ≤ b → b ≤ c → a ≤ c := by
  intro hab hbc q hq
  exact hbc (hab hq)

theorem lt_iff_le_not_le {a b : DCut} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  constructor
  . intro h
    rw[lt_of_le] at h
    have ⟨ h1, h2 ⟩ := h
    constructor
    . exact h.right
    . intro h3
      exact h1 (anti_symm h.right h3)
  . intro ⟨ h1, h2 ⟩
    rw[le_of_lt] at h1
    apply Or.elim h1
    . intro h
      rw[h] at h2
      exact False.elim (h2 refl)
    . intro h
      exact h

instance pre_order_inst : Preorder DCut :=
  ⟨ @refl, @trans, @lt_iff_le_not_le ⟩

instance poset_inst : PartialOrder DCut :=
  ⟨ @anti_symm ⟩
```
 Next we prove that cuts form a total order, and instantiate this fact with the TotalOrder class from Mathlib. 
```lean
theorem total {x y : DCut} : x ≤ y ∨ y ≤ x := by
  by_cases h : x ≤ y
  . exact Or.inl h
  . apply Or.inr
    simp_all[le_inst]
    intro b hb
    rw[Set.subset_def] at h
    simp at h
    obtain ⟨ a, ⟨ ha1, ha2 ⟩ ⟩ := h
    exact x.dc b a ⟨ le_of_lt (a_lt_b hb ha2), ha1 ⟩

instance total_inst : IsTotal DCut (· ≤ ·) := ⟨ @total ⟩
```
 The total order property allows crisply define positive and negative numbers. 
```lean
def isPos (x : DCut) : Prop := 0 < x
def isNeg (x : DCut) : Prop := x < 0
```
 We can also use the total order property to prove that `DCut` is _Trichotomous_, that is, that for all `x` and `y`, either `x ≤ y`, `y ≤ x`, or `x=y`. 
```lean
theorem trichotomy (x y: DCut) : x ≤ y ∨ x = y ∨ y ≤ x := by
  apply Or.elim (@total x y)
  . intro h
    exact Or.symm (Or.inr h)
  . intro h
    exact Or.inr (Or.inr h)

theorem trichotomy_lt (x y: DCut) : x < y ∨ x = y ∨ y < x := by
  have := trichotomy x y
  simp[le_of_lt] at this
  aesop

instance trichotomous_inst : IsTrichotomous DCut (· ≤ ·) := ⟨ trichotomy ⟩

instance trichotomous_inst' : IsTrichotomous DCut (· < ·) := ⟨ trichotomy_lt ⟩
```
 ## Theorems About Zero and One 
```lean
theorem zero_in_pos {a : DCut} (ha : 0 < a) : 0 ∈ a.A := by
  obtain ⟨ h1, h2 ⟩ := ha
  simp at h1
  rw[DCut.ext_iff] at h1
  have h21 := Set.ssubset_iff_subset_ne.mpr ⟨h2, h1⟩
  have ⟨ x, ⟨ hx1, hx2 ⟩ ⟩ := (Set.ssubset_iff_of_subset h2).mp h21
  simp[zero_rw,odown] at hx2
  exact a.dc 0 x ⟨ hx2, hx1 ⟩

theorem pos_has_zero {a : DCut} : 0 < a ↔ 0 ∈ a.A := by
  constructor
  . intro h
    exact zero_in_pos h
  . simp[lt_inst,DCut.ext_iff]
    intro h
    constructor
    . intro h1
      rw[←h1] at h
      simp[zero_rw,odown] at h
    . intro q hq
      simp[zero_rw,odown] at hq
      apply a.dc q 0
      exact ⟨ by exact _root_.le_of_lt hq, h ⟩


theorem non_neg_in_pos {a : DCut} (ha : 0 < a) : ∃ x ∈ a.A, 0 < x := by
  have h0 := zero_in_pos ha
  exact a.op 0 h0

theorem zero_notin_neg {a : DCut} (ha : a < 0) : 0 ∉ a.A := by
  intro h
  simp[lt_inst] at ha
  have ⟨ h1, h2 ⟩ := ha
  have : 0 ∈ A 0 := h2 h
  simp[zero_rw,odown] at this

@[simp]
theorem zero_lt_one : (0:DCut) < 1 := by
  simp[lt_inst]
  apply And.intro
  . intro h
    simp[DCut.ext_iff,zero_rw,one_rw,odown,Set.ext_iff] at h
    have := h 0
    simp_all
  . intro q hq
    simp_all[zero_rw,one_rw,odown]
    linarith

@[simp]
theorem zero_le_one : (0:DCut) ≤ 1 := by
  simp[le_inst]
  intro q hq
  simp_all[zero_rw,one_rw,odown]
  linarith

instance zero_le_one_inst : ZeroLEOneClass DCut := ⟨ zero_le_one ⟩

theorem not_gt_to_le {a : DCut} : ¬ 0 < a ↔ a ≤ 0 := by
  constructor
  . have := trichotomy_lt 0 a
    apply Or.elim this
    . intro h1 h2
      simp_all
    . intro h1 h2
      simp_all
      apply le_of_lt.mpr
      rw[Eq.comm]
      exact h1
  . intro h1 h2
    apply le_of_lt.mp at h1
    simp_all[DCut.ext_iff,lt_inst]
    have ⟨ h3, h4 ⟩ := h2
    simp_all
    apply Or.elim h1
    . intro h
      exact h3 (id (Eq.symm h))
    . intro ⟨ h5, h6 ⟩
      have : A 0 = a.A := by exact Set.Subset.antisymm h4 h6
      exact h3 this

theorem has_ub (a : DCut) : ∃ x, x ∉ a.A ∧ ∀ y ∈ a.A, y < x := by
  obtain ⟨ x, hx ⟩ := a.nf
  use! x, hx
  intro y hy
  exact a_lt_b hy hx

theorem in_down {p q:ℚ} (h : p < q) : p ∈ odown q := by
  simp[odown]
  exact h

theorem in_zero {q:ℚ} (h: q<0) : q ∈ A 0 := by
  simp[zero_rw]
  exact in_down h

theorem in_one {q:ℚ} (h: q<1) : q ∈ A 1 := by
  simp[one_rw]
  exact in_down h
```
 ## Supporting Reasoning by Cases

Later, in the chapter on multiplication, it will be useful to reason about combinations of non-negative and negative cuts. With one cut `a`, there are two possibilities: `0 ≤ a` and `a < 0`. For two cuts there are four possibilities, and for three cuts, there are eight possibilities.

The following two definitions list all possible cases for two and three cuts respectively. 
```lean
def two_ineq_list (a b : DCut) :=
  (0 ≤ a ∧ 0 ≤ b) ∨
  (a < 0 ∧ 0 ≤ b) ∨
  (0 ≤ a ∧ b < 0) ∨
  (a < 0 ∧ b < 0)

def two_ineq_nn_list (a b: DCut) :=
  (0 < a ∧ 0 < b) ∨ a = 0 ∨ b = 0

def three_ineq_list (a b c : DCut) :=
  (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨
  (a < 0 ∧ 0 ≤ b ∧ 0 ≤ c) ∨
  (0 ≤ a ∧ b < 0 ∧ 0 ≤ c) ∨
  (0 ≤ a ∧ 0 ≤ b ∧ c < 0) ∨
  (a < 0 ∧ b < 0 ∧ 0 ≤ c) ∨
  (a < 0 ∧ 0 ≤ b ∧ c < 0) ∨
  (0 ≤ a ∧ b < 0 ∧ c < 0) ∨
  (a < 0 ∧ b < 0 ∧ c < 0)

def three_ineq_nn_list (a b c : DCut) :=
  (0 < a ∧ 0 < b ∧ 0 < c) ∨ a = 0 ∨ b = 0 ∨ c = 0
```
 Next we show that these statements are tautologies. The goal is to be able to use the definitions in tactic mode, as in:
```hs
rcases @two_ineqs a b with ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩
repeat
simp
```

We start with a theorem that can be used to rewrite `x<0` as `¬0≤x`.

```lean
theorem neg_t {x : DCut} : x < 0 ↔ ¬0 ≤ x := by
  have := trichotomy_lt 0 x
  simp_all[le_of_lt]
  constructor
  . intro h
    exact ⟨ ne_of_gt h, not_lt_of_gt h ⟩
  . tauto

theorem neg_t' {x : DCut} : 0 < x ↔ ¬x ≤ 0 := by
  have := trichotomy_lt 0 x
  simp_all[le_of_lt]
  constructor
  . intro h
    exact ⟨ ne_of_gt h, not_lt_of_gt h ⟩
  . tauto
```
 Then the proofs are straightforward. To see how these are used later, see the proofs of commutativity and associativity of multiplication. 
```lean
theorem lt_imp_le {x y : DCut} : x < y → x ≤ y := by simp[lt_of_le]

theorem two_ineqs (a b : DCut) : two_ineq_list a b := by
  simp[two_ineq_list,neg_t]
  tauto

theorem three_ineqs (a b c : DCut) : three_ineq_list a b c := by
  simp[three_ineq_list,neg_t]
  tauto

theorem two_nn_ineqs {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b)
  : two_ineq_nn_list a b := by
  simp[two_ineq_nn_list,neg_t]
  simp[le_of_lt] at ha hb
  tauto

theorem three_nn_ineqs {a b c : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  : three_ineq_nn_list a b c := by
  simp[three_ineq_nn_list,neg_t]
  simp[le_of_lt] at ha hb hc
  tauto
```
 **Exercise**:

1. Show that `ofRat` is indeed an order embedding, that is `x ≤ y → ofRat x ≤ ofRat y` for all rational numbers `x` and `y`.

1. Let `(A,B)` be a cut. Show that for any `q ∈ A`, there exists a function `f : ℕ → A` such that<br>
a) `q i ∈ A`<br>
b) `q < f 0` and for all `i`, `f i < f j`



<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
