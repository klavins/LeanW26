
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Completions.lean'>Code</a> for this chapter</span>
 # The Dedekind-MacNeille Completion

A **completion** is an embedding of a partially ordered set into a complete lattice. It allows one to "fill in the gaps" in an ordered set so that, for example, limit points exist. The real numbers, for example, are the completion of the rational numbers.

In this chapter we describe the the Dedekind-MacNeille (DM) Completion, which is a generalization of the Dedekind cuts method of constructing the reals to the case of any ordered set. In particular, we define `DM P` for any poset `P`. If `P=ℚ`, the result is isomorphic to the reals with `-∞` and `∞`, but the approach works for any poset.

Formally, the Dedekind-MacNeille completion `DM P` is defined to be the family of subsets of `S ⊆ P` that are closed with respect to the closure operator `λ P ↦ lower (upper P)`.  
```lean
@[ext]
structure DM (P : Type u) [Poset P] where
  val : Set P
  h : lower (upper val) = val
```
 Our goal is to show that `DM P` is a complete lattice for any `P`. We can easily show that `DM P` is a poset under the usual `⊆` ordering.  
```lean
instance DM.poset {P : Type u} [Poset P] : Poset (DM P) :=
  ⟨
    λ ⟨ A, hA ⟩ ⟨ B, hB ⟩ => A ⊆ B,
    by
      intro ⟨ A, _ ⟩
      exact Set.Subset.refl A,
    by
      intro ⟨ A, hA ⟩ ⟨ B, hB ⟩ h1 h2
      simp_all
      exact Set.Subset.antisymm h1 h2,
    by
      intro ⟨ A, hA ⟩ ⟨ B, hB ⟩ ⟨ C, hC ⟩ h1 h2
      exact Set.Subset.trans h1 h2
  ⟩
```
 In fact, the `DM` structure forms what Davey and Priestly call a _topped intersection structure_, which we will show is a Complete Lattice with a particular definition for the meet and join that we define next. 
 ## The Meet

We define a _meet_ for `DM P`, which is just set-intersection taken over a subset of `DM P`.

$$
\mathrm{meet}(S) = \bigcap_{A ∈ S} A.
$$

To prove this definition of _meet_ gives `DM P` a semilattice structure, we have to show the result of such an intersection satisfies the `upper-lower` condition. First we define the intersection of a subset of `DM P` (i.e. of a set of sets taken from `DM P`). 
```lean
def DM.inter {P : Type u} [Poset P] (S : Set (DM P)) := { x | ∀ T ∈ S, x ∈ T.val }
```
 We will need to use the simple fact that the interection of a family ot sets is a subset of every member of the family. 
```lean
theorem DM.inter_sub {P : Type u} [Poset P] {S : Set (DM P)}
  : ∀ T ∈ S, inter S ⊆ T.val := by
  intro T hT x hx
  exact hx T hT
```
 Using this fact, we can show the intersection preserves the `lower-upper` property required of elements of `DM P`. 
```lean
theorem DM.inter_in_dm {P : Type u} [Poset P] {S : Set (DM P)}
  : lower (upper (inter S)) = inter S := by
    apply Set.eq_of_subset_of_subset
    . intro x hx T hT
      rw[←T.h]
      exact sub_low (sub_up (inter_sub T hT)) hx
    . exact sub_lu (inter S)
```
 And with this theorem we can finally define the _meet_ as a function from `Set (DM P)` into `DM P`. Recall, that to do so we need to not only supply the operation `inter` on `S`, but also proof that `inter S` is in `DM P`. 
```lean
def DM.meet {P : Type u} [Poset P] (S : Set (DM P)) : DM P :=
  ⟨ inter S, inter_in_dm ⟩
```
 To show that `DM P` is a Complete Semilattice, we need to show that this definition of `meet` is indeed a greatest lower bound. We do so in two steps, first showing the `meet S` is a lower bound of `S` and second showing it is a greatest lower bound of `S`. 
```lean
theorem DM.meet_lb {P : Type u} [Poset P] :
  ∀ S : Set (DM P), IsLB S (meet S) := by
  intro S T hT
  apply DM.inter_sub
  exact hT

theorem DM.meet_greatest {P : Type u} [Poset P]
  : ∀ S : Set (DM P), ∀ w, (IsLB S w) → w ≤ meet S := by
  intro S W h
  intro x hx T hT
  exact h T hT hx
```
 Now we have everything we need to instantiate the Complete Semilattice class. 
```lean
instance DM.csl {P : Type u} [Poset P] : CompleteSemilattice (DM P) :=
  ⟨ meet, meet_lb, meet_greatest ⟩
```
 ## The Join

Next we define a join. It would be nice to simply define the join of `S` to be the union of all sets in `S`, but the result would in general not be closed with respect to the `lower-upper` operator used to define `DM P`. To get around this, the join for `DM P` is defined to be the intersection of sets containing the union.

$$
\mathrm{join}(S) = \bigcap \left \\{ B \in DM(P) \\;|\\; \bigcup_{A ∈ S} A \subseteq B \right \\}
$$

First we define the union. 
```lean
def DM.union {P : Type u} [Poset P] (S : Set (DM P)) := { x | ∃ T ∈ S, x ∈ T.val }
```
 We will need an intermediate theorem analogous to the intersection theorem proved for the meet. This one shows that the intersection of a set of sets is contained in each set. 
```lean
theorem DM.inter_union_dm {P : Type u} [Poset P] {S : Set (DM P)}
  : ∀ C ∈ {C : DM P| union S ⊆ C.val}, inter {C | union S ⊆ C.val} ⊆ C.val := by
    intro C hC x hx
    exact hx C hC
```
 We use this theorem to show the meet is closed. 
```lean
theorem DM.union_in_dm {P : Type u} [Poset P] {S : Set (DM P)}
  : lower (upper (inter {C | union S ⊆ C.val})) = inter {C | union S ⊆ C.val} := by
  apply Set.eq_of_subset_of_subset
  . intro x hx T hT
    rw[←T.h]
    exact sub_low (sub_up (inter_union_dm T hT)) hx
  . apply sub_lu
```
 The join operator is then be defined as follows. 
```lean
def DM.join {P : Type u} [Poset P] (S : Set (DM P)) : DM P :=
  ⟨ inter { C | union S ⊆ C.val }, union_in_dm ⟩
```
 To show `DM P` is a Complete Lattice, we need to show the join is a least upper bound, which we do in two steps. 
```lean
theorem DM.join_ub {P : Type u} [Poset P] :
  ∀ S : Set (DM P), IsUB S (join S) := by
  intro S T hT x hx W hW
  simp[union,Set.subset_def] at hW
  exact hW x T hT hx

theorem DM.join_least {P : Type u} [Poset P]
  : ∀ S : Set (DM P), ∀ W, (IsUB S W) → join S ≤ W := by
  intro S W h x hx
  apply hx W
  intro y ⟨ Q, ⟨ h1, h2 ⟩ ⟩
  exact h Q h1 h2
```
 Now we have everything we need to show `DM P` is a Complete Lattice. 
```lean
instance DM.lattice {P : Type u} [Poset P] : CompleteLattice (DM P) :=
  ⟨ join, join_ub, join_least ⟩
```
 ## Completion Map

The mapping from `P` into `DM P` is defined implicitly in the construction of `DM P`. Explicitly, the embedding is definition by the `down` operator.  That is, the map `λ x ↦ down x` is the ordering embedding that wintesses the completion. To show this, we prove that `down x` is closed under the `lower-upper` closure operator. 
```lean
theorem DM.down_is_dm {P : Type u} [Poset P] {x : P}
  : lower (upper (down x)) = down x :=
  by
    apply Set.eq_of_subset_of_subset
    . intro y hy
      exact hy x fun a a ↦ a
    . intro a ha
      simp_all[upper,lower]
```
 This theorem then allows us to formally define the embedded. We call it `make`, because it allows us to _make_ an element of `DM P` out of any element `x ∈ P`. 
```lean
def DM.make {P : Type u} [Poset P] (x : P) : DM P := ⟨ down x, down_is_dm ⟩
```
 Finally, we prove that `make` is an order embeddeding (as defined in [Maps](./Maps.md)). 
```lean
theorem DM.make_embed {P : Type u} [Poset P]
  : OrderEmbedding (make : P → DM P) := by
  intro x y
  constructor
  . intro h z hz
    exact Poset.trans z x y hz h
  . intro h
    simp[make,down,le_inst,Poset.le] at h
    exact h x (Poset.refl x)
```
 ## Completion of a Total Order

If `P` is a totally ordered set, then its completion ought to be totally ordered as well. We show that here. We start with a useful theorem stating the fact that all elements of `DM P` are downward closed. 
```lean
theorem dm_down_close {P : Type u} [Poset P] {X : DM P}
  : ∀ y, ∀ x ∈ X.val, y ≤ x → y ∈ X.val := by
  intro y x hx hyx
  rw[←X.h] at hx ⊢
  intro z hz
  apply Poset.trans y x z hyx (hx z hz)
```
 Now we show the main result. 
```lean
theorem dm_total_order {P : Type u} [TotalOrder P]
  : ∀ (x y : DM P), Comparable x y := by

  intro X Y
  by_cases h : X.val ⊆ Y.val

  . exact Or.inl h

  . -- Obtain an x in X - Y
    obtain ⟨ x, ⟨ hx, hxny ⟩ ⟩ := Set.not_subset.mp h

    -- Show y ≤ x using the fact that Y is closed
    rw[←Y.h] at hxny
    simp[lower] at hxny
    obtain ⟨ y, ⟨ hy, hcomp ⟩ ⟩ := hxny
    have hyx : y ≤ x := by
      apply Or.elim (TotalOrder.comp x y)
      . intro h
        exact False.elim (hcomp h)
      . exact id

    -- Show Y ⊆ down x using transitivity of ≤ in P
    have hYdx : Y.val ⊆ down x := by
      intro b hb
      exact Poset.trans b y x (hy b hb) hyx

    -- Show down x ⊆ X using the helper theorem above
    have hdxX: down x ⊆ X.val := by
      intro b hb
      exact dm_down_close b x hx hb

    -- Show Y ⊆ X using transitivity of ⊆
    apply Or.inr
    intro q hq
    exact hdxX (hYdx hq)
```
 Using this theorem, we can instantiate the total order class for `DM P` for any totally ordered `P`. 
```lean
instance {P : Type u} [TotalOrder P] : TotalOrder (DM P) := ⟨ dm_total_order ⟩
```
 We can show a useful theorem stating that every element besides top has a principal upper bound. 
```lean
theorem DM.not_top_is_bounded {P : Type u} [Poset P] {x : DM P}
  : x ≠ CompleteLattice.top → ∃ q : P, x ≤ DM.make q := by
  intro h

  have h1 : x.val ≠ Set.univ := by
    by_contra h2
    simp[CompleteLattice.top,CompleteSemilattice.inf,DM.meet,DM.inter,DM.ext] at h
    apply h (DM.ext h2)

  have ⟨ q, hq ⟩ : ∃ q, q ∈ Set.univ \ x.val := by
    by_contra h
    simp at h
    exact h1 (Set.eq_univ_iff_forall.mpr h)

  have h2 : ¬q ∈ x.val := by exact Set.not_mem_of_mem_diff hq

  rw[←x.h] at h2
  simp[upper,lower] at h2
  obtain ⟨ r, ⟨ hr, hrq ⟩ ⟩ := h2

  use r
  simp[DM.make,down,le_inst,Poset.le]

  intro y hy
  simp
  exact hr y hy
```
 We can also show that every element besides `bot` is non-empty. 
```lean
theorem DM.not_bot_to_exists {P : Type u} [Poset P] {x : DM P}
  : x ≠ CompleteLattice.bot → ∃ v, v ∈ x.val := by
  intro h
  apply Set.nonempty_iff_ne_empty.mpr
  intro hxb
  simp[CompleteLattice.bot,CompleteLattice.sup,DM.join,DM.inter,DM.union] at h
  have : {x | ∀ (T : DM P), x ∈ T.val} = ∅ := by
    ext q
    constructor
    . simp
      by_contra hn
      simp at hn
      have := hn x
      simp_all[Set.mem_empty_iff_false]
    . simp

  simp[this] at h
  exact h (DM.ext hxb)
```
 ## Examples

### A Finite Example


```lean
namespace Temp

inductive MyPoset where
  | a : MyPoset
  | b : MyPoset

open MyPoset

def myle (x y : MyPoset) := x = y

instance : Poset MyPoset :=
  ⟨ myle, by simp[myle], by simp[myle], by simp[myle] ⟩

theorem my_poset_all {x : MyPoset} : x ∈ ({a, b}: Set MyPoset) := by
  match x with
  | a => exact Set.mem_insert a {b}
  | b => exact Set.mem_insert_of_mem a rfl

def top : DM MyPoset := ⟨
  { a, b },
  by
    apply Set.eq_of_subset_of_subset
    . intro x h
      exact my_poset_all
    . intro x hx
      simp[lower,upper]
      intro y h1 h2
      match x with
      | a => exact h1
      | b => exact h2
  ⟩

def bot : DM MyPoset := ⟨
  ∅,
  by
    apply Set.eq_of_subset_of_subset
    . intro x hx
      simp[lower,upper] at hx
      have h1 := hx a
      have h2 := hx b
      rw[h1] at h2
      apply noConfusion h2
    . exact Set.empty_subset (lower (upper ∅))
⟩

example : ∃ b : DM MyPoset, ∀ x, b ≤ x := by
  use bot
  intro S y hy
  exact False.elim hy

end Temp
```
 ## Exercises

1) Show `DM ℕ` is isomorphic to `ℕ ∪ {∞}` where `x ≤ ∞` for all `x`. 

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
