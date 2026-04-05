
Sets
===


Types vs Sets
===

Type theory and set theory are different foundational theories for mathematics.

**Types**
- A judgement `x : α` is a primitive
- Membership is defined by typing rules
- A type is a syntactic object
- Predicates are types

**Sets**
- Membership `∈` is primitive
- Membership is defined by a predicate
- A set is a semantic object
- Predicates are meta-logical formulas

At best we can only simulate sets in type theory using definitions and notation.


Types as Sets
===

**Option 1:** Express sets directly as types

- Membership `x ∈ S` is `x : S`

- Subsets are subtypes
```
class Subtype {α : Sort u} (p : α → Prop)
  val : α
  property : p val
```

For example:



<div class="lean-code" data-start-line="56" data-end-line="57"><pre><code>def Evens := Subtype (fun n =&gt; ∃ k, n = 2*k)
example : Evens := ⟨ 14, by use 7 ⟩</code></pre></div>

 In fact, Lean defines nice syntax for `Subtype`, which looks like set builder notation.  

<div class="lean-code" data-start-line="61" data-end-line="62"><pre><code>def Evens&#x27; := { n // ∃ k, n = 2*k }
example : Evens&#x27; := ⟨ 14, by use 7 ⟩</code></pre></div>


Uses of Subtypes
===

Many objects in Lean and Mathib are defined as subtypes:



<div class="lean-code" data-start-line="72" data-end-line="74"><pre><code>#print NNRat               -- def NNRat : Type := { q : Rat // 0 ≤ r }
#print NNReal              -- def NNReal : Type := { r : Real // 0 ≤ r }
#print SpecialLinearGroup  -- def ... := ... fun R V ... ↦ { u // LinearEquiv.det u = 1 }</code></pre></div>


And the basic pattern of including a predicate in a structure is common, as in:
```lean
structure Subgroup (G : Type u) [Group G] where
  p : G → Prop
  one_in : p 1
  inv_in : p x → p x⁻¹
  mul_in : p a → p b → p a * b
```

These kinds of constructions allow you to package the proof that an element is a
member of the `Subtype` in the sub type itself.



Issues with Types as Sets
===

Defining set operations is at best complicated:


<div class="lean-code" data-start-line="101" data-end-line="107"><pre><code>--hide
namespace Temp
--unhide

def Subtype.Intersection.{u} {α : Type u} {p q : α → Prop}
  (A : Type u) (B : Type u){_hA : A = Subtype p} {_hB : B = Subtype q} :=
  { x // p x ∧ q x }</code></pre></div>

 For example, given 

<div class="lean-code" data-start-line="111" data-end-line="112"><pre><code>def A := { n // n &gt; 4 }
def B := { n // n &gt; 5 }</code></pre></div>

 here is `A ∩ B`: 

<div class="lean-code" data-start-line="116" data-end-line="117"><pre><code>def C := Subtype.Intersection (p := (· &gt; 4)) (q := (· &gt; 5))
  (_hA := by simp[A]) (_hB := by simp[B]) A B</code></pre></div>

 Now to show that, for exampe `6 ∈ A ∩ B`, we do: 

<div class="lean-code" data-start-line="121" data-end-line="125"><pre><code>example : C := ⟨ 6, ⟨ by simp, by simp ⟩ ⟩

--hide
end Temp
--unhide</code></pre></div>


Exercise
===

<ex /> Define



<div class="lean-code" data-start-line="135" data-end-line="135"><pre><code>def Evens.add (x y : Evens) : Evens := sorry</code></pre></div>

 and prove 

<div class="lean-code" data-start-line="139" data-end-line="140"><pre><code>def Evens.add_assoc {x y z : Evens}
  : add x (add y z) = add (add x y) z := sorry</code></pre></div>


Predicates as Sets
===

**Option 2**: In `def A := { n // n > 4 }` the predicate `n>4` is buried in the expression.
What if we just used use the predicate directly, as in


<div class="lean-code" data-start-line="150" data-end-line="151"><pre><code>def A (n : ℕ) := n &gt; 4
def B (n : ℕ) := n &gt; 5</code></pre></div>

 and then put 

<div class="lean-code" data-start-line="155" data-end-line="155"><pre><code>def C (n : ℕ) := A n ∧ B n</code></pre></div>

 whch looks quite close to `C = A ∩ B`. 

How the Mathlib's Set Library is Defined
===
Let's rebuild the set library.
<div class='fn'>Everything below is in a temporary namespace to avoid conflicts.</div>



<div class="lean-code" data-start-line="168" data-end-line="180"><pre><code>--hide
namespace Temp2
--unhide

def Set (α : Type) := α → Prop

def Set.member {α : Type} (x : α) (S : Set α) := S x
def Set.inter {α : Type} (A B : Set α) (x : α) := A x ∧ B x
def Set.union {α : Type} (A B : Set α) (x : α) := A x ∨ B x

scoped infix:20 &quot; ∈ &quot; =&gt; Set.member
scoped infixl:60 &quot; ∩ &quot; =&gt; Set.inter
scoped infixl:40 &quot; ∪ &quot; =&gt; Set.union</code></pre></div>


Example Revisited
===
Using the new definitions, we can write:


<div class="lean-code" data-start-line="188" data-end-line="194"><pre><code>def A : Set ℕ := (· &gt; 4)
def B : Set ℕ := (· &gt; 5)

example : 6 ∈ A ∩ B := by   -- This is just the statement A 6 ∧ B 6
  apply And.intro
  · simp[A]
  · simp[B]</code></pre></div>


The Subset Relation
===

The subset relation is just implication:


<div class="lean-code" data-start-line="203" data-end-line="205"><pre><code>def Set.subset {α : Type} (A B : Set α) : Prop := ∀ x, A x → B x

infixl:40 &quot; ⊆ &quot; =&gt; Set.subset</code></pre></div>

 And proofs look like first order logic 

<div class="lean-code" data-start-line="209" data-end-line="211"><pre><code>example {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  exact hx.left</code></pre></div>

 In fact, using the `change` tactic, you can make the goal look like FOL: 

<div class="lean-code" data-start-line="215" data-end-line="218"><pre><code>example {α : Type} (A B : Set α) : A ∩ B ⊆ A := by
  change ∀ x, A x ∧ B x → A x
  intro x hx
  exact hx.left</code></pre></div>


Proving Set Equalites
===

To show two sets are equal, it is enough to show each is a subset of the other.

This theorem uses the axiom `propext` which says `∀ {a b : Prop}, (a ↔ b) → a = b`



<div class="lean-code" data-start-line="230" data-end-line="240"><pre><code>theorem subset_antisymm_iff {α : Type} {A B : Set α}
  : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  apply Iff.intro
  · intro h
    simp only [h, and_self]
    intro x hx
    exact hx
  · intro ⟨ ha, hb ⟩
    funext x
    apply propext
    exact ⟨ ha x, hb x ⟩</code></pre></div>

 The name `antisym` comes from the observation that the subset relation is *antisymmetric*. 

An Example Set Equality
===


<div class="lean-code" data-start-line="249" data-end-line="255"><pre><code>example {α : Type} (A B : Set α) : A ∩ B = B ∩ A := by
  apply subset_antisymm_iff.mpr
  apply And.intro
  · intro x hx
    exact ⟨ hx.right, hx.left ⟩
  · intro x hx
    exact ⟨ hx.right, hx.left ⟩</code></pre></div>


Complements and Differences
===
Complements and differences are what you would expect.


<div class="lean-code" data-start-line="264" data-end-line="268"><pre><code>def Set.uninv {α : Type} : Set α := fun _ =&gt; True
def Set.compl {α : Type} (S : Set α) := fun x =&gt; ¬S x
postfix:95 &quot; ᶜ &quot; =&gt; Set.compl
def Set.diff {α : Type} (A B : Set α) := A ∩ Bᶜ
infixl: 55 &quot; - &quot; =&gt; Set.diff  -- Lean uses `\` but I couldn&#x27;t get that to work</code></pre></div>

 For example, we can show the relationship between compliment and universe. 

<div class="lean-code" data-start-line="272" data-end-line="280"><pre><code>example {α : Type} {A : Set α} : Aᶜ = Set.univ - A := by
  apply subset_antisymm_iff.mpr
  constructor
  · intro x hx
    constructor
    · trivial
    · exact hx
  · intro x ⟨ _, hc ⟩
    exact hc</code></pre></div>


Powersets
===
The set of all subsets of a set can be defined using the subset relation:


<div class="lean-code" data-start-line="288" data-end-line="288"><pre><code>def Set.power {α : Type} (S : Set α) : Set (Set α) := fun A =&gt; A ⊆ S</code></pre></div>

 Here is a nice example property: 

<div class="lean-code" data-start-line="292" data-end-line="297"><pre><code>example {α : Type} (A B : Set α)
  : A ⊆ B → Set.power A ⊆ Set.power B := by
  intro hab S hS x Sx
  apply hab
  apply hS
  exact Sx</code></pre></div>

 This operation and many more are defined in Mathlib's *extensive* `Set` Library:
- [Definitions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html)
- [Set Operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Operations.html)
- [Basic Properties](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Basic.html)



<div class="lean-code" data-start-line="306" data-end-line="308"><pre><code>--hide
end Temp2
--unhide</code></pre></div>


Set Builder Notation
===

Mathlib provides a powerful set builder notation.

For example:



<div class="lean-code" data-start-line="320" data-end-line="327"><pre><code>#check { n : ℕ  | n &gt; 2 }
#check fun n =&gt; n &gt; 2

#check { 2*n | n &gt; 2 }
#check fun x =&gt; ∃ n &gt; 2, 2*n = x

#check { (x,y) | Prime x ∧ Prime y ∧ x + 1 = y }
#check fun p : ℕ × ℕ =&gt; Prime p.1 ∧ Prime p.2 ∧ p.1 + 1 = p.2</code></pre></div>


Exercises
===


<div class="lean-code" data-start-line="335" data-end-line="336"><pre><code>universe u
variable (α β : Type u) {A B C : Set α} {D E : Set β}</code></pre></div>


<ex /> Using first order logic (and not Mathlib's set theorems), show:



<div class="lean-code" data-start-line="343" data-end-line="344"><pre><code>example : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := sorry
example : A ⊆ B → B ⊆ C → A ⊆ C := sorry</code></pre></div>

 <ex /> Lean defines the image of `f` with respect to `A`, denoted `f '' A`,
to be the set `{f x | x ∈ A}`. Show:



<div class="lean-code" data-start-line="351" data-end-line="351"><pre><code>example {f : α → β} : f &#x27;&#x27; (A ∪ B) = f &#x27;&#x27; A ∪ f &#x27;&#x27; B := sorry</code></pre></div>

 <ex /> Lean defines the preimage of `f` with respect to `A`, denoted
`f⁻¹' A` to be the set `{x | ∃ y, f x = y}`. Show,



<div class="lean-code" data-start-line="358" data-end-line="358"><pre><code>example {f : α → β} : f⁻¹&#x27; (D ∩ E) = f⁻¹&#x27; D ∩ f⁻¹&#x27; E := sorry</code></pre></div>


Finite Sets
===

Defining a type for *finite* sets is an interesting challenge. Here are some options:

- **Finite types**
    - Define `Fin n := {0,1,2,...,n-1}`
    - Define typeclass `Fintype α` as having a bijection `α ≃ Fin n`
    - Cons: subsets, unions, etc are hard to define

- **Lists**
    - Create a structure with a `List` and a property requiring no duplicates
    - Cons: List equality depends on ordering

- **Equivalence Classes of Lists** (Lean's Approach)
    - Define perumutation an equivalence relation between lists
    - Take the quotient
    - Pros: It works
    - Cons: It's complicated



Fin
===

The easiest way to make a type that has exactly `n` elements is:



<div class="lean-code" data-start-line="392" data-end-line="404"><pre><code>--hide
namespace Temp3
--unhide

structure Fin (n : ℕ) where
  val : ℕ
  isLt : val &lt; n

example : Fin 5 := ⟨ 3, by decide ⟩

--hide
end Temp3
--unhide</code></pre></div>


Lean defines quite a bit of infrastructure around this type. For example,


<div class="lean-code" data-start-line="410" data-end-line="413"><pre><code>def x : Fin 10 := 1
def y : Fin 10 := 2

#eval 2*x + y               -- 4</code></pre></div>

 Although it doesn't always do what you would expect : 

<div class="lean-code" data-start-line="417" data-end-line="417"><pre><code>#eval x + 10*y              -- 1 (modular addition)</code></pre></div>

 But what if we want a finite type that has any type of element, not just integers?


Finite Types
===

We can definte a typeclass that registers a type `α` as finite by exhibiting a
bijection between `Fin n` and `α`. We wrap this into a `Prop`-valued typeclass
as follows:



<div class="lean-code" data-start-line="431" data-end-line="432"><pre><code>class inductive Finite (α : Type u) : Prop where
  | intro {n : ℕ} : α ≃ Fin n → Finite α</code></pre></div>

 For example 

<div class="lean-code" data-start-line="436" data-end-line="445"><pre><code>inductive Spin where | up | dn

def Spin.equiv_fin2 : Spin ≃ Fin 2 := {
  toFun x   := match x with | up =&gt; 0 | dn =&gt; 1,
  invFun n  := match n with | 0 =&gt; up | 1 =&gt; dn,
  right_inv := by grind,
  left_inv  := by grind
}

instance Spin.is_finite : Finite Spin := ⟨ Spin.equiv_fin2 ⟩</code></pre></div>


Lean's Finset
===

A `Finset` in Lean is a finite collection of elements all of the same type with
set-like operations:


<div class="lean-code" data-start-line="455" data-end-line="461"><pre><code>def R : Finset ℚ := {1/2, 1/4, 1/8, 1/16}
def S : Finset ℚ := {-3,-2,-1,0,1,2,3}

#eval R ∩ S
#eval R \ S

#eval insert 4 (insert (-4) R)       --  {-4,-3,-2,-1,0,1,2,3,4}</code></pre></div>

 Under the hood, a `Finset` is a structure: 

<div class="lean-code" data-start-line="466" data-end-line="469"><pre><code>def X : Finset ℕ := {
  val := [1,2,3],                      -- A `Multiset`, which derives from a `List`
  nodup := by simp                     -- A proof the list has no duplicates
}</code></pre></div>


In general you do not have a set defined by a predicate, or operations like


<div class="lean-code" data-start-line="475" data-end-line="476"><pre><code>#check_failure Rᶜ
#check_failure ({ n : ℕ | n &lt; 10 } : Finset ℕ)</code></pre></div>


Exercises
===

<ex /> Prove the following properties of `Fin`:



<div class="lean-code" data-start-line="487" data-end-line="489"><pre><code>example : Fin 0 → False := sorry
example (x : Fin 2) : x = 0 ∨ x = 1 := sorry
example (n : ℕ) (x y : Fin n) : x = y ↔ x.val = y.val := sorry</code></pre></div>


<ex /> Define the equivalence



<div class="lean-code" data-start-line="496" data-end-line="496"><pre><code>def equiv_subtype {n : ℕ} : Fin n ≃ { x : ℕ | x &lt; n } := sorry</code></pre></div>


<ex /> Use the above equivalence to show



<div class="lean-code" data-start-line="503" data-end-line="503"><pre><code>theorem equiv_same_size {n m : ℕ} (eq : Fin n ≃ Fin m) : n = m := sorry</code></pre></div>


<ex /> (Optional) Prove the pigeonhole principal (constructively, whithout the classical axiom).



<div class="lean-code" data-start-line="510" data-end-line="511"><pre><code>theorem pp {m n : ℕ} {f : Fin m → Fin n}
  : m &gt; n → ∃ a b, a ≠ b ∧ f a = f b := sorry</code></pre></div>


Exercise
===

<ex /> (Optional) Suppose we define the natural numbers as follows:


<div class="lean-code" data-start-line="520" data-end-line="523"><pre><code>def zero {α : Type u} : Set α := ∅
def one {α : Type u} : Set (Set α) := {zero}
def two {α : Type u} : Set (Set (Set α)) := {one}
-- etc.</code></pre></div>

 How do you define the successor function? Addition? Etc? 

<div class="lean-code" data-start-line="527" data-end-line="529"><pre><code>--hide
end LeanW26
--unhide</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

