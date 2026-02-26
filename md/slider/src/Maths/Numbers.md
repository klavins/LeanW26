
Numbers by Construction
===


Natural Numbers
===

```lean
inductive Nat where
  | zero                         -- Least element
  | succ : Nat → Nat             -- Successor function

open Nat
```

With basic operations

```lean
def add (x y : Nat) : Nat :=
  match x with
  | zero => y
  | succ k => succ (add k y)

def mul (x y : Nat) : Nat :=
  match x with
  | zero => zero
  | succ k => add (mul k y) y

def sub : Nat → Nat → Nat
  | n, zero => n
  | n, succ j => sub n j
```

Properties of Addition and Multiplication
===

Addition is associative and commutative and multiplication
is associative, commutative, and distributive. One starts with basic
properties and builds up to these. For example,

```lean
theorem zero_add (n : Nat) : add zero n = n := by rfl

theorem add_zero (n : Nat) : add n zero = n := by induction n with
  | zero => rfl
  | succ k ih =>
    unfold add
    rw[ih]

theorem add_succ (m n : Nat) : succ (add m n) = add m (succ n) := by
  induction m with
  | zero => rw[zero_add,add]
  | succ k ih =>
     unfold add
     rw[ih]

theorem add_comm (m n : Nat) : add m n = add n m := by
  induction m with
  | zero => rw[zero_add,add_zero]
  | succ k ih =>
    conv => lhs; unfold add
    rw[ih,add_succ]
```

Ordering
===
Ordering is defined as an iductive predicate, giving two proof rules.

```lean
inductive le (n : Nat) : Nat → Prop
  | refl     : le n n
  | step {m} : le n m → le n (succ m)

def lt (x y : Nat) : Prop := le (succ x) y
```
 The properties of the less than relation can then be built up from
simple theorems. For example, 
```lean
theorem le_succ {n : Nat} : le n (succ n) := le.step le.refl

theorem zero_is_least {n : Nat} : le zero n := by
  induction n with
  | zero => exact le.refl
  | succ k ih => exact le.step ih

theorem zero_is_only_least (n : Nat) : le n zero ↔ n = zero := by
  constructor
  · intro h; cases h; rfl
  · intro h; rw[h]; exact le.refl
```

Further Properties of Less-Than
===

```lean
theorem succ_not_le_zero {k : Nat} : ¬le (succ k) zero := by
  --brief
  intro h
  cases h
  --unbrief

theorem le_trans {x y z : Nat} : le x y → le y z → le x z := by
  --brief
  intro hxy hyz
  induction hyz with
  | refl => exact hxy
  | @step m hyz' ih =>
    exact le.step ih
  --unbrief

lemma le_succ_cases {x y : Nat} :
  le x (succ y) → (x = succ y) ∨ le x y := by
  --brief
  intro h
  cases h with
  | refl   => exact Or.inl rfl
  | step h => exact Or.inr h
  --unbrief

lemma not_succ_le_self (n : Nat) : ¬ le (succ n) n := by
  --brief
  intro h
  induction n with
  | zero => exact succ_not_le_zero h
  | succ k ih =>
    have := le_succ_cases (x := succ (succ k)) (y := k) h
    cases this with
    | inl h1 =>
      rw[succ.injEq] at h1
      rw[h1] at ih
      exact ih le.refl
    | inr h1 =>
      exact ih (le_trans le_succ h1)
  --unbrief

theorem le_antisymm {x y : Nat} : le x y → le y x → x = y := by
  --brief
  intro hxy hyx
  cases hxy with
  | refl => repeat rfl
  | @step k hk =>
    cases hyx with
    | refl => rfl
    | @step j hj =>
      apply False.elim
      apply not_succ_le_self k
      apply le_trans hj (le_trans _ hk)
      exact le_succ
  --unbrief
```

Exercises
===

<ex /> Show addition on `Nat` is associative, multiplication is associative, commutative,
and that addition and multiplication distribute. You will need to build put a
series of similer theorems to show these cleanly.

<ex /> Show that `le` is a total order:


```lean
theorem le_total (x y : Nat) : le x y ∨ le y x := sorry
```

<ex /> Show that `le` on `Nat` is well-founded:


```lean
theorem wf (S : Nat → Prop) (Sne : ∃ q, S q)
  : ∃ m, (S m ∧ ∀ n, S n → le m n) := sorry


--hide
end Temp
--unhide
```

Lean's Integers
===

In Lean, integers are defined inductively with

```
inductive Int : Type where
  | ofNat   : Nat → Int
  | negSucc : Nat → Int
```

The *negative successor* is required to avoid two representatives of `0`.

For example:


```lean
#eval Int.ofNat 1       --  1 : ℤ
#eval Int.ofNat 0       --  0 : ℤ
#eval Int.negSucc 0     -- -1 : ℤ
#eval Int.negSucc 1     -- -2 : ℤ
```

Bourbaki Integers
===
As an alternative construction of the integers, where we take pairs
`(x,y)` with `x-y` being nonnegative integer when `x ≥ y` and negative
otherwise.


```lean
@[ext]
structure Pair where
  p : Nat
  q : Nat
```
 Since there are multiple representations of each intger, we define
an equivalence relation: 
```lean
def eq (x y : Pair) : Prop := x.p + y.q = x.q + y.p
```
 For example 
```lean
example : eq ⟨1,2⟩ ⟨2,3⟩ := rfl          -- ways to write -1
example : eq ⟨3,2⟩ ⟨20,19⟩ := rfl        -- ways to write 1
```

Forming the Quotient
===

First we prove `eq` is an equivalence relation.

```lean
theorem eq_refl (u : Pair) : eq u u := by
  simp[eq]; linarith

theorem eq_symm {v w : Pair} : eq v w → eq w v := by
  intro h; simp_all[eq]; linarith

theorem eq_trans {u v w : Pair} : eq u v → eq v w → eq u w := by
  intro h1 h2; simp_all[eq]; linarith

instance eq_equiv : Equivalence eq := ⟨ eq_refl, eq_symm, eq_trans ⟩
```
 Then we instantiate the `Setoid` instance and form the quotient: 
```lean
instance pre_int_setoid : Setoid Pair :=  ⟨ eq, eq_equiv ⟩
def Bint := Quotient pre_int_setoid
def mk (w : Pair) : Bint := Quotient.mk pre_int_setoid w

namespace Bint
```

Using The New Bint Type
===

Basic examples now work

```lean
example : mk ⟨ 1, 2 ⟩ = mk ⟨ 2, 3 ⟩ := by
  apply Quotient.sound
  rfl
```
 And we can instantiate some type classes: 
```lean
instance zero_sint : Zero Bint := ⟨ mk ⟨ 0,0 ⟩ ⟩
instance one_inst : One Bint := ⟨ mk ⟨ 1,0 ⟩ ⟩
instance of_nat_inst {n : ℕ} :OfNat Bint n := ⟨ mk ⟨ n, 0 ⟩ ⟩

#check (0:Bint)
#check (1:Bint)
#check (123:Bint)
```

Operations on Bint
===

We can lift operations on `Pair` to `Bint`. For example, here is negation:

```lean
def pre_negate (x : Pair) : Pair := ⟨ x.q, x.p ⟩

theorem pre_negate_respects (x y : Pair) :
  x ≈ y → mk (pre_negate x) = mk (pre_negate y) := by
  intro h
  apply Quot.sound
  exact h.symm

def pre_negate' (x : Pair) : Bint := mk (pre_negate x)
def negate (x : Bint) : Bint := Quotient.lift pre_negate' pre_negate_respects x
```
 We may register our negation function wit the `Neg` class.  
```lean
instance int_negate : Neg Bint := ⟨ negate ⟩
```
 Now we can use negative integers. 
```lean
#check -mk ⟨2,1⟩
#check -(1:Int)
```

Basic Equivalence with Int
===

```lean
def bint_to_int : Bint → Int :=
  Quotient.lift (fun p => (p.p : Int) - p.q) (by
    intro a b h
    have : a.p + b.q = a.q + b.p := h
    linarith)

def int_to_bint (x : Int) : Bint := match x with
    | Int.ofNat k => mk ⟨ k, 0 ⟩
    | Int.negSucc k => mk ⟨ 0, k+1 ⟩

def bint_int_equiv : Bint ≃ Int := {
  toFun := bint_to_int,
  invFun := int_to_bint
  left_inv := sorry,
  right_inv := sorry
}
```

Transporting Theorems
===

```lean
lemma bint_int_equiv_neg (x : Bint) : bint_int_equiv (-x) = -bint_int_equiv x := by
  induction x using Quotient.inductionOn with
  | h y =>
    simp?[bint_to_int,bint_int_equiv]
    exact Int.neg_inj.mp rfl

theorem neg_neg (x : Bint) : - -x = x := by
  apply bint_int_equiv.injective
  rw [bint_int_equiv_neg, bint_int_equiv_neg]
  exact Int.neg_neg (bint_int_equiv x)
```

Exercises
===

<ex /> Define `pre_add` for `Pair` and `add` for `Bint`.

<ex /> Show associativity for `add` directly.

<ex /> Show associativity for `add` by transporting from `Int`.


```lean
--hide
end Bint
--unhide
```

Lean's Rationals
===

```lean
structure Rat where
  mk' ::
  num : Int
  den : Nat := 1
  den_nz : den ≠ 0 := by decide
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq, Hashable
```

```lean
def mkRat (num : Int) (den : Nat) : Rat :=
  if den_nz : den = 0 then { num := 0 } else Rat.normalize num den den_nz
```


Exercises
===

<ex /> Define an equivalence relation on `Pair` with `x.p * y.q = x.q * y.p` and form the
quotient to define an alternative rational number type, `Brat`.

<ex /> Define addition on `Brat` and show it it commutative using
(a) a direct proof and (b) by transporting from Lean`'s `Rat.



Cauchy Sequences
===

To define the Real Numbers, we start with sequences of Rationals.

We define a sequence `ℕ → ℚ` to be *Cauchy* if terms in the sequence eventually
become arbitrarily close to each other.


```lean
@[ext]
structure CauchySeq where
  σ : ℕ → ℚ
  is_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n m : ℕ,
              n > N → m > N → abs (σ n - σ m) < ε
```
 For example, a constant sequence is `Cauchy`.  
```lean
instance Cauchy.zero_inst : Zero CauchySeq := ⟨
  fun _ => 0,
  by
    intro ε hε
    use 1
    intro n m hn hm
    simp[hε]
⟩

--hide
instance Cauchy.one_inst : One CauchySeq := ⟨
  fun _ => 1,
  by
    intro ε hε
    use 1
    intro n m hn hm
    simp[hε]
⟩
--unhide
```

<div class='fn'>This construction is an incompletely simplification of how
Mathlib defines the real numbers. For a complete description, see the
<a href="https://github.com/leanprover-community/mathlib4/blob/d20aa7a3b0563797673a3465f67586af5a5aede9/Mathlib/Data/Real/Basic.lean#L33-L37">source code</a>.</div>



Operations on Cauchy Sequences
===
The following is a standard proof from most Real Analysis texts:

```lean
def Cauchy.add (s1 s2 : CauchySeq) : CauchySeq := ⟨
  fun n => s1.σ n +  s2.σ n, by
  intro ε hε
  have ⟨ N1, h1' ⟩ := s1.is_cauchy (ε/2) (by exact half_pos hε)
  have ⟨ N2, h2' ⟩ := s2.is_cauchy (ε/2) (by exact half_pos hε)
  use N1 + N2
  intro m n gm gn
  have h1'' := h1' n m (by linarith) (by linarith)
  have h2'' := h2' n m (by linarith) (by linarith)
  simp_all[abs_lt]
  exact ⟨ by linarith, by linarith ⟩
⟩
```
 We can show, for example 
```lean
theorem zero_plus_zero : Cauchy.add 0 0 = 0 := by
  ext n
  simp[Cauchy.add]
  rfl
```

Sequence Equivalence
===

Two sequences are equivalent in the *Cauchy* sense if:

```lean
def Cauchy.eq (x y : CauchySeq) :=
  ∀ ε > 0, ∃ N, ∀ m n,
  m > N → n > N → |x.σ n - y.σ m| < ε
```
 One can show, for example: 
```lean
theorem Cauchy.eq_refl {x : CauchySeq} : Cauchy.eq x x := by
  intro ε hε
  have ⟨ N, h ⟩ := x.is_cauchy ε hε
  use N
  intro m n hm hn
  have h' := h n m hn hm
  exact h'
```
 And eventually prove `Cauchy.eq` is an equivalence relation so that
the reals become the quotient of `CauchySeq` w.r.t this relation. 

Exercises
===

<ex /> Finish the proof that `Cauchy.eq` is an equivalence relation,
and form the quotient to get a `CauchyReal` type.

<ex /> Complete the definition


```lean
def cauchy_mul (x y : CauchySeq) : CauchySeq := ⟨
  fun n => (x.σ n)*(y.σ n),
  sorry,
⟩
```

and lift it to  `CauchyReal`.


<ex /> Define


```lean
def sqrt2_seq (n : Nat) : ℚ := match n with
  | Nat.zero => 1
  | Nat.succ k => (sqrt2_seq k + 2 / (sqrt2_seq k))/2
```
 and complete the definition 
```lean
def sqrt2 : CauchySeq := ⟨
   sqrt2_seq,
   sorry
⟩
```

Exercise
===

<ex /> Define less than or equal for sequences as


```lean
def leq (x y : CauchySeq) := Cauchy.eq x y ∨ ∃ N, ∀ n > N, x.σ n ≤ y.σ n
```
 then show 
```lean
example : leq 1 sqrt2 := sorry
```

Dedekind Reals
===
An alternative construction of the reals is Dedekind's method, which does
not require quotients.

First, we define a structure to capture the precise definition of a cut `A ⊆ ℚ`.
We require that A is nonempty, that it is not ℚ, that it is
downward closed, and that is an open interval. 
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
 We have only defined the lower part, `A` of a cut.
The upper part of the cut, `B` is defined simply: 
```lean
def DCut.B (c : DCut) : Set ℚ := Set.univ \ c.A
```

<div class='fn'>A standard reference for Dedekind cuts is Rudin's Principles of Mathematics.
In the 3rd edition, cuts are defined on pages 17-21.</div>



ofRat
===

All rational numbers are also real numbers via the map that identifies a
rational `q` with the interval `(∞,q)` of all rationals less than `q`.
We call this set `odown q`, where `odown` is meant to abbreviate
`open, downward closed`. 
```lean
def odown (q : ℚ) : Set ℚ := { y | y < q }
```
 To prove that `odown q` is a Dedekind cut requires we show it is nonempty,
not `ℚ` itself, downward closed, and open.  
```lean
def ofRat (q : ℚ) : DCut := ⟨
  odown q,
  by use q-1; simp[odown],
  by use q+1; simp[odown],
  by intro x y ⟨ hx, hy ⟩; simp_all[odown]; linarith,
  by
    intro x hx
    use (x+q)/2
    simp_all[odown]
    exact ⟨ by linarith, by linarith ⟩
  ⟩
```

Basic Instances
===

Casting

```lean
instance rat_cast_inst : RatCast DCut := ⟨ fun x => ofRat x ⟩
instance nat_cast_inst : NatCast DCut := ⟨ fun x => ofRat x ⟩
instance int_cast_inst : IntCast DCut := ⟨ fun x => ofRat x ⟩
```
 Zero and One 
```lean
instance zero_inst : Zero DCut := ⟨ ofRat 0 ⟩
instance one_inst : One DCut := ⟨ ofRat 1 ⟩
instance inhabited_inst : Inhabited DCut := ⟨ 0 ⟩
```
 Nontriviality 
```lean
theorem zero_ne_one : (0:DCut) ≠ 1 := by
  intro h
  simp[DCut.ext_iff,odown,Set.ext_iff] at h
  have h0 := h (1/2)
  have h1 : (1:ℚ)/2 < 1 := by linarith
  have h2 : ¬(1:ℚ)/2 < 0 := by linarith
  exact h2 (h0.mpr h1)

instance non_triv_inst : Nontrivial DCut := ⟨ ⟨ 0, 1, zero_ne_one ⟩ ⟩
```

Addition
===
Operators on the Dedekind reals are not nearly as straightforward
as with the Cauchy reals. Here is addition:

```lean
def presum (a b : DCut) :=  { z | ∃ x ∈ a.A, ∃ y ∈ b.A, x+y=z }
```
 The first property required be a cut is straigtforward: 
```lean
theorem presum_ne {a b : DCut} :  ∃ q, q ∈ presum a b := by
  obtain ⟨ x, hx ⟩ := a.ne
  obtain ⟨ y, hy ⟩ := b.ne
  exact ⟨ x+y, ⟨ x, ⟨ hx, ⟨ y, ⟨ hy, by linarith ⟩ ⟩ ⟩ ⟩ ⟩
```

Addition does not Result in all of ℚ
===

We start with some helper theorems.

```lean
theorem not_in_a_in_b {c : DCut} {q : ℚ} : q ∉ c.A → q ∈ c.B := by simp[B]
theorem not_in_b_in_a {c : DCut} {q : ℚ} : q ∉ c.B → q ∈ c.A := by simp[B]

theorem b_gt_a {c : DCut} {x y : ℚ} : x ∈ c.A → y ∈ c.B → x < y := by
  intro hx hy
  simp[B] at hy
  by_contra h
  exact hy (c.dc y x ⟨ Rat.not_lt.mp h, hx ⟩)
```
 Then we have, 
```lean
theorem presum_nf {a b : DCut} : ∃ q, q ∉ presum a b := by
    obtain ⟨ x, hx ⟩ := a.nf
    obtain ⟨ y, hy ⟩ := b.nf
    use x+y
    intro h
    obtain ⟨ s, ⟨ hs, ⟨ t, ⟨ ht, hst ⟩ ⟩ ⟩ ⟩ := h
    have hs' := b_gt_a hs (not_in_a_in_b hx)
    have ht' := b_gt_a ht (not_in_a_in_b hy)
    linarith
```

The Sum of Two Cuts is Open
===

```lean
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
  · exact hx'
  · use y'
    apply And.intro
    · exact hy'
    · linarith
```

The Sum of Two Cuts is Downward Closed
===

```lean
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
```

Instances for Addition
===

```lean
def sum (a b : DCut) : DCut :=
  ⟨ presum a b, presum_ne, presum_nf, presum_dc, presum_op ⟩

instance hadd_inst : HAdd DCut DCut DCut:= ⟨ sum ⟩
instance add_inst : Add DCut := ⟨ sum ⟩
```

And here is an example property, which requires mainly rearrangment.

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
```

Exercises
===

<ex /> Show


```lean
theorem sum_comm {a b : DCut} : a + b = b + a := sorry
theorem sum_zero_left {a : DCut} : 0 + a = a :=  sorry
theorem sum_zero_right {a : DCut} : a + 0 = a := sorry
```


<ex /> Define the instances


```lean
instance lt_inst : LT DCut := ⟨ fun x y => x ≠ y ∧ x.A ⊆ y.A ⟩
instance le_inst : LE DCut := ⟨ fun x y => x.A ⊆ y.A ⟩
```
 And show 
```lean
theorem sum_pos_pos {a b : DCut} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := sorry
theorem sum_nneg_nneg {a b : DCut} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := sorry
```

<ex /> Use this definition


```lean
def preneg (c : DCut) : Set ℚ := { x | ∃ a < 0, ∃ b ∉ c.A, x = a-b }
```

To build subtraction for `DCut`.

```lean
--hide
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

