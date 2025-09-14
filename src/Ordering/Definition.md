
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Definition.lean'>Code</a> for this chapter</span>
 # Overview

An **order relation** on a set `A` is a predicate `A → A → Prop` that captures some notion of order. A familiar example is the the _less than_ relation on the natural numbers: 
```lean
#check 1 ≤ 2
```
 where `<` is shorthand for 
```lean
#check Nat.le       -- ℕ → ℕ → Prop
```
 `Nat.le` is an example of a **total order** on a set, meaning any two elements `x` and `y` are related (i.e. `x≤y` or `y≤x`). This need not be the case in general. For example, the subset relation `⊆` on sets is only a **partial order**, because one can find sets `A` and `B` for which neither `A ⊆ B` or `B ⊆ A`. 
```lean
namespace Temp

def A : Set ℕ := {1,2}
def B : Set ℕ := {3,4}

example : ¬A ⊆ B ∧ ¬B ⊆ A := by
  apply And.intro
  . intro h
    have h1a: 1 ∈ A := by simp[A]
    have h1b := h h1a
    simp[B] at h1b
  . intro h
    have h3b: 3 ∈ B := by simp[B]
    have h3a := h h3b
    simp[A] at h3a

end Temp
```
 You will encounter many other examples of orderings besides these two, some of which we will get to in later sections. For now, we aim like to define a hierarchy of types of orders that capture their similarities and differences, defining a general theory of orders. A side goal here is to show how Lean's heirachy machinery works from the point of view of defining a _new_ hierarchy instead of using someone else's hierarchy.

Most of this material comes from the book _Introduction to Lattices and Order_ by Davey and Priestly. 
 ## Partial Orders

A **partially ordered set** or **poset** is a set and a _less-than_ ordering relation on the set that requires pretty much the minimum one might expect from a binary relation for it to be called an ordering: the relation needs to be reflexive, anti-symmetric, and transitive (see [Relations](../Relations.html)). Using a new Lean `class`, we define a class of types that have a less-than relation with these three properties. 
```lean
class Poset (α : Type u) where
  le : α → α → Prop
  refl : ∀ x, le x x
  anti_sym : ∀ x y, le x y → le y x → x = y
  trans : ∀ x y z, le x y → le y z → le x z
```
 ### Example : The Natural Numbers

Lean's standard library has all of these properties defined for natural numbers. Therefore, we can assert that `ℕ` is a `poset` by instantiating the `Poset` class as follows. 
```lean
instance : Poset ℕ := ⟨ Nat.le, @Nat.le.refl, @Nat.le_antisymm, @Nat.le_trans⟩
```
 ### Example : Sets

Lean's standard library also has all of these properties defined for sets.  
```lean
instance {A: Type u} : Poset (Set A) := ⟨
  Set.Subset,
  Set.Subset.refl,
  λ _ _ h1 h2 => Set.Subset.antisymm h1 h2,
  λ _ _ _ h1 h2 => Set.Subset.trans h1 h2
⟩
```
 ## Poset Notation

Simply having the `Poset` class defined does not give us much, however. Thus, the main goal of this section is to develop theorems that, for example, apply to any `Poset`, define specific kinds of `Poset`, or that relate `Posets` to each other.

To state these theorems cleaning, we first register some notation with Lean. Instantiating the `LE` and `LT` classes in Lean's standard library allow us to use `≤`, `≥`, `<`, and `ge` on elements of our `Poset` type. Notice how these instances are declared. We have to supply a Type `A`, and require that it has been instantiated as a `Poset`. 
```lean
instance le_inst {A : Type u} [Poset A] : LE A := ⟨ Poset.le ⟩
instance lt_inst {A : Type u} [Poset A] : LT A := ⟨ λ x y => x ≤ y ∧ x ≠ y ⟩

example {A : Type u} [Poset A] (x:A) := x ≥ x
```
 ## Total Orders

A **total order** is a `Poset` with the added requirement that any two elements are comparable. 
```lean
def Comparable {P : Type u} [Poset P] (x y: P) := x ≤ y ∨ y ≤ x

class TotalOrder (T: Type u) extends Poset T where
  comp: ∀ x y : T, Comparable x y
```
 The natural numbers are a total order, which is shown via a theorem in Lean's standard library. : 
```lean
instance nat_total_order : TotalOrder ℕ :=
  ⟨ Nat.le_total ⟩
```
 Sets are not a total order, however. 
```lean
example : ∃ x y : Set ℕ, ¬Comparable x y := by
  apply Exists.intro {1}
  apply Exists.intro {2}
  simp[Comparable]
```
 ## (Meet) Semilattices

A `Semilattice` is a `Poset` for which there exists a greatest lower bound function, usually called `meet`, for every pair of points `x` and `y`. Then we extend the hierarchy with a new class of orders. 
```lean
class Semilattice (L : Type u) extends Poset L where
  meet : L → L → L
  lb : ∀ x y, meet x y ≤ x ∧ meet x y ≤ y
  greatest : ∀ x y w, w ≤ x → w ≤ y → w ≤ meet x y
```
 For example, the natural numbers form a semilattice. So do sets. 
```lean
instance nat_semi_lattice : Semilattice ℕ :=
  ⟨
    Nat.min,
    by
      intro x y
      exact ⟨ Nat.min_le_left x y, Nat.min_le_right x y⟩,
    by
      intro x y _ h1 h2
      exact Nat.le_min_of_le_of_le h1 h2
  ⟩

instance set_semi_lattice {α : Type u}: Semilattice (Set α) :=
  ⟨
    Set.inter,
    by
      intro A B
      apply And.intro
      . intro x hx
        exact Set.mem_of_mem_inter_left hx
      . intro x hx
        exact Set.mem_of_mem_inter_right hx,
    by
      intro A B _ h1 h2 _ hc
      exact ⟨ h1 hc, h2 hc ⟩
  ⟩
```
 ## Lattices

If all pairs of elements also have a least upper bound, then the `Poset` is called a `Lattice`. The least upper bound function is called the **join**. 
```lean
class Lattice (L : Type u) extends Semilattice L where
  join : L → L → L
  ub : ∀ x y, (x ≤ join x y ∧ y ≤ join x y)
  least : ∀ x y w, x ≤ w → y ≤ w → join x y ≤ w
```
 Both ℕ and Sets are Lattices as well. The joing for ℕ is `Nat.max` and the join for sets is `Set.union`. 
```lean
instance nat_lattice : Lattice ℕ :=
  ⟨
    Nat.max,
    by
      intro x y
      exact ⟨ Nat.le_max_left x y, Nat.le_max_right x y ⟩,
    by
      intro x y _ h1 h2
      exact Nat.max_le_of_le_of_le h1 h2
  ⟩

instance set_lattice {α : Type u}: Lattice (Set α) :=
  ⟨
    Set.union,
    by
      intro A B
      . exact Set.union_subset_iff.mp (λ  _ a => a),
    by
      intro A B C h1 h2 c hc
      apply Or.elim hc
      . exact λ h3 => h1 h3
      . exact λ h3 => h2 h3
  ⟩
```
 As an example of a semilattice that is not a lattice is the so-called [information ordering](./Information.html) on partial functions, decribed in a separate chapter. 
 ## Notation for Lattices

The meet and join of two elements `x` and `y` of a poset are denonted `x ⊓ y` and `x sup y`. The notation classes for these operations are called `Min` and `Max`, even though you do not have to use them for actual mins and maxes. 
```lean
instance Semilattice.and_inst {L : Type u} [Semilattice L] : Min L :=
  ⟨ meet ⟩

instance Lattice.or_inst {L : Type u} [Lattice L] : Max L :=
  ⟨ join ⟩
```
 ## Meet and Join Example Theorems

Here are two straightforward theorems about meets and joins that test out the definitions and notation. They follow from the definitions of greatest lower bound, least upper bound, anti-symmetry, and reflexivity. 
```lean
theorem Semilattice.meet_idempotent {L : Type u} [Semilattice L] (x : L) : x ⊓ x = x := by
  have ⟨ h1, h2 ⟩ := lb x x
  have h4 := greatest x x x (Poset.refl x) (Poset.refl x)
  exact Poset.anti_sym (x ⊓ x) x h1 h4

theorem Lattice.join_idempotent {L : Type u} [Lattice L] (x : L) : x ⊔ x = x := by
  have ⟨ h1, h2 ⟩ := ub x x
  have h4 := least x x x (Poset.refl x) (Poset.refl x)
  apply Poset.anti_sym (x ⊔ x) x h4 h1
```
 ## Complete Lattices

Lattices require that every pair of elements have a greatest lower bound and leaset upper bound. A Complete Lattice requires that every set have such bounds. An example of a Complete Lattice is `Set A`, which we show after defining Complete Lattices. 
```lean
def IsLB {P : Type u} [Poset P] (S : Set P) (lb : P) := ∀ x ∈ S, lb ≤ x

class CompleteSemilattice (L : Type u) extends Poset L where
  inf : Set L → L
  lb : ∀ S, IsLB S (inf S)
  greatest : ∀ S w, (IsLB S w) → w ≤ inf S

def IsUB {P : Type u} [Poset P] (S : Set P) (ub : P) := ∀ x, x ∈ S → x ≤ ub

class CompleteLattice (L : Type u) extends CompleteSemilattice L where
  sup : Set L → L
  ub : ∀ S, IsUB S (sup S)
  least : ∀ S, ∀ w, (IsUB S w) → sup S ≤ w
```
 Example: The set of subsets of a given set `A` is a complete lattice, which we show in two steps using straighforward proofs. 
```lean
instance set_csl {A : Type u}: CompleteSemilattice (Set A) :=
  ⟨
    λ S => { x | ∀ T ∈ S, x ∈ T },
    by
      intro S T h x hx
      dsimp at hx
      exact hx T h,
    by
      intro S T h x hx R hR
      exact h R hR hx
  ⟩

instance set_cl {A : Type u}: CompleteLattice (Set A) :=
  ⟨
    λ S => { x | ∃ T ∈ S, x ∈ T },
    by
      intro S T h x hx
      apply Exists.intro T
      exact ⟨h, hx⟩,
    by
      intro S T h x hx
      dsimp at hx
      obtain ⟨ R, ⟨ h1, h2 ⟩ ⟩ := hx
      exact h R h1 h2
  ⟩
```
 ## Complete Lattices are Bounded

Notice that in the definition of `inf` the condition `(IsLB S w)` in  `(IsLB S w)→ w ≤ inf S` is trivially satisfied if `S = ∅`. Therefore, `w ≤ inf ∅` for all `w`, meaning that `inf ∅` is a top element. Similarly, `sup ∅` is a bottom element. We can conclude that every Complete Lattice is bounded, as shown by the next two theorems.  
```lean
@[simp]
def CompleteLattice.bot {L : Type u} [CompleteLattice L] : L :=
  sup (∅:Set L)

@[simp]
def CompleteLattice.top {L : Type u} [CompleteLattice L] : L :=
  CompleteSemilattice.inf (∅:Set L)

theorem CompleteLattice.is_bot {L : Type u} [CompleteLattice L]
  : ∀ x : L, bot ≤ x := by
  intro x
  apply CompleteLattice.least ∅ x
  simp[IsUB]

theorem CompleteLattice.is_top {L : Type u} [CompleteLattice L]
  : ∀ x : L, x ≤ top := by
  intro x
  apply CompleteSemilattice.greatest ∅ x
  simp[IsLB]
```
 ## Complete Lattices are Lattices

We can also show that a complete lattice is a lattice by restricting `inf` and `sup` to act on sets of size two. 
```lean
instance CompleteSemilattice.inst_sl {L : Type u} [CompleteSemilattice L]
  : Semilattice L := ⟨
    λ x y => inf {x,y},
    by
      intro x y
      apply And.intro <;>
      apply lb <;>
      simp,
    by
      intro x u z h1 h2
      apply greatest
      simp[IsLB, h1, h2]
  ⟩

instance CompleteLattice.inst_l {L : Type u} [CompleteLattice L]
  : Lattice L := ⟨
    λ x y => sup {x,y},
    by
      intro x y
      apply And.intro <;>
      apply ub <;>
      simp,
    by
      intro x u z h1 h2
      apply least
      simp[IsUB, h1, h2]
  ⟩
```
 ## Hierarchy
```
     Lattice     CL
        |         |
    Semilattice  CSL   Total Order
             \    |    /
                Poset
```





<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
