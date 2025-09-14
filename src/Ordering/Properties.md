
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Properties.lean'>Code</a> for this chapter</span>
 ## Simple Properties 
```lean
theorem eq_to_le {P : Type u} [Poset P] {x y : P} : x = y → x ≤ y := by
  intro h
  rw[h]
  exact refl y
```
 ## Up Sets and Down Sets

The set of all elements above (below) a given element `x:P` is called the up (down) set of `x`. 
```lean
def up {P : Type u} [Poset P] (x : P) : Set P := { y | x ≤ y }
def down {P : Type u} [Poset P] (x : P) : Set P := { y | y ≤ x }
```
 A set that is upwardly (downwardly) closed is called an Up (Down) set. We define predicates on subsets of a Poset to capture these properties. These are a bit tricky to read. The first one says that if `x` is any element and there is a `y` in some upward closed set `S` that is less than or equal to it, then `x` must also be in `S`. The second statement about downward closed sets is similar.  
```lean
def UpSet {P : Type u} [Poset P] (S : Set P) := ∀ x, (∃ y ∈ S, y ≤ x) → x ∈ S
def DownSet {P : Type u} [Poset P] (S : Set P) := ∀ x, (∃ y ∈ S, x ≤ y) → x ∈ S
```
 Simple theorems relating these definitions can now be proved. The next two, for example, show that up (down) sets are upwardly (downwardly) closed. 
```lean
theorem up_is_up {P : Type u} [Poset P] (x : P) : UpSet (up x) := by
  intro z ⟨ y, ⟨ h1, h2 ⟩  ⟩
  simp_all[Set.mem_def,up]
  exact trans x y z h1 h2

theorem down_is_down {P : Type u} [Poset P] (x : P) : DownSet (down x) := by
  intro z ⟨ y, ⟨ h1, h2 ⟩  ⟩
  simp_all[Set.mem_def,down]
  apply trans z y x h2 h1
```
 Upward closed sets are not just those built from a single element. For example, the union of two upwardly closed sets is also upwardly closed. 
```lean
theorem up_union {P : Type u} [Poset P] (x y: P) : UpSet ((up x) ∪ (up y)) := by
  intro w ⟨ z, ⟨ h1, h2 ⟩ ⟩
  apply Or.elim h1
  . intro h3
    exact Or.inl (trans x z w h3 h2)
  . intro h3
    apply Or.inr (trans y z w h3 h2)
```
 ## Lower and Upper Sets 
```lean
def upper {P : Type u} [Poset P] (A : Set P) : Set P :=
 { x | ∀ a ∈ A, a ≤ x }

def lower {P : Type u} [Poset P] (A : Set P) : Set P :=
 { x | ∀ a ∈ A, x ≤ a }

-- 1
theorem sub_ul {P : Type u} [Poset P] (A : Set P)
  : A ⊆ upper (lower A) := by
  intro x hx a ha
  exact ha x hx

theorem sub_lu {P : Type u} [Poset P] (A : Set P)
  : A ⊆ lower (upper A) := by
  intro x hx a ha
  exact ha x hx

theorem eq_to_sub {P : Type u} [Poset P] (A : Set P)
  : lower (upper A) ⊆ A → lower (upper A) = A := by
  intro h
  exact Set.eq_of_subset_of_subset h (sub_lu A)

-- 2
theorem sub_up {P : Type u} [Poset P] {A B : Set P}
  : A ⊆ B → upper B ⊆ upper A := by
  intro h b hb a ha
  exact hb a (h ha)

-- 3
theorem sub_low {P : Type u} [Poset P] {A B : Set P}
  : A ⊆ B → lower B ⊆ lower A := by
  intro h b hb a ha
  exact hb a (h ha)

-- 4
theorem up_ulu {P : Type u} [Poset P] {A : Set P}
 : upper A = upper (lower (upper A)) := by
 apply Set.eq_of_subset_of_subset
 . intro a ha b hb
   exact hb a ha
 . intro a ha b hb
   exact ha b fun a a ↦ a b hb

-- 5
theorem low_lul {P : Type u} [Poset P] {A : Set P}
 : lower A = lower (upper (lower A)) := by
 apply Set.eq_of_subset_of_subset
 . intro a ha b hb
   exact hb a ha
 . intro a ha b hb
   exact ha b fun a a ↦ a b hb
```
 ## Minimal and Maximal Elements

A **minimal** element of a set `S ⊆ P` is one for which no other elements of `S` are smaller. 
```lean
def Minimal {P : Type u} [Poset P] (S : Set P) (m : P) := ∀ x ∈ S, x ≤ m → x = m
```
 Minimal elements are not necessarily unique. The following example shows that when `x` and `y` are unrelated, either one of them is minimal. 
```lean
example {P : Type u} [Poset P] (x y: P) : (¬x≤y ∧ ¬y≤x) → Minimal {x,y} x := by
  intro ⟨h1, h2⟩ z h3 h4
  apply Or.elim h3
  . exact id
  . intro h5
    rw[h5] at h4
    exact False.elim (h2 h4)
```
 On the other hand, a **minimum** element is a unique minimal element. 
```lean
def Minimum {P : Type u} [Poset P] (S : Set P) (m : P) := ∀ x ∈ S, m ≤ x
```
 The most minimal element of a `Poset` is usually called `bot`. 
```lean
def is_bot {P : Type u} [Poset P] (x : P) := ∀ y, x ≤ y

theorem bot_minimum {P : Type u} [Poset P] (m : P) : is_bot m → Minimum Set.univ m := by
  intro hb x hm
  simp_all[is_bot]
```
 These definitions apply to maxima as well. 
```lean
def Maximal {P : Type u} [Poset P] (S : Set P) (m : P) := ∀ x ∈ S , m ≤ x → x = m
def Maximum {P : Type u} [Poset P] (S : Set P) (m : P) := ∀ x ∈ S, x ≤ m
def is_top {P : Type u} [Poset P] (x : P) := ∀ y, y ≤ x
```
 ## Chains and Anti-Chains

A chain is a totally ordered subset of a poset. 
```lean
def Chain {P : Type u} [Poset P] (S : Set P) := ∀ x ∈ S, ∀ y ∈ S, x ≤ y ∨ y ≤ x
```
 For example, the upset of any natural number is a chain. 
```lean
example {n : ℕ} : Chain (up n) := by
  intro x hx y hy
  exact Nat.le_total x y
```
 An antichain is a set of uncomparable elements. 
```lean
def AntiChain {P : Type u} [Poset P] (S : Set P) := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (¬x ≤ y ∧ ¬y ≤ x)
```
 For example, the set of singletons each containing a different natural number is an anti-chain. 
```lean
def my_anti_chain : Set (Set ℕ) := { {n} | n : ℕ }

example : AntiChain my_anti_chain := by
  simp[my_anti_chain]
  intro Sm ⟨ m, hsm ⟩ Sn ⟨ n, hsn ⟩ hmn
  simp[le_inst]
  apply And.intro
  . intro h
    rw[←hsm,←hsn] at h
    rw[←hsm,←hsn] at hmn
    exact hmn (congrArg singleton (h rfl))
  . intro h
    rw[←hsm,←hsn] at h
    rw[←hsm,←hsn] at hmn
    exact id (Ne.symm hmn) (congrArg singleton (h rfl))
```
 ## Exercises 
 1) Show the rational numbers ℚ with the natural order ≤ form a Poset 
```lean
instance : Poset ℚ := ⟨ λ x y => x ≤ y, sorry, sorry, sorry ⟩
```
 2) Show the upper set (0,1) is [1,∞) 
```lean
example : upper {x:ℚ | 0 < x ∧ x < 1} = { x | 1 ≤ x } := sorry
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
