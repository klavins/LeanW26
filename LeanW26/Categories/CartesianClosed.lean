import Mathlib

namespace LeanW26

open CategoryTheory

/-
Why Category Theory?
===

**Q**: What do the following mathematical topics all have in common?

```hs
Sets             Graphs
Types            Groups
Vector Spaces    Automata
Formal Proofs    Computable Functions
```

**A**: They all have:
- Objects
- Transformations of objects into other objects
- Relationships with each other

Can we talk about all these branches of math using the same concepts, to mathematically define
what they have in common and how they are different?

Category Theory
===

A **Category** is a data structure with the following elements

- **Objects**, usually denoted `X`, `Y`, ...
- **Morphisms** `f : X ⟶ Y`

And with the properties:

- **Identity**: For every `X`, `idX : X ⟶ X` is a morphism
- **Composition**: If `f : X ⟶ Y` and `g : Y ⟶ Z` are arrows, then so is `f ≫ g : X ⟶ Z`
- **Composition with Identites**: `idX ≫ f = f ≫ idX = f`.
- **Associativity**: `(f ≫ g) ≫ h = f ≫ (g ≫ h)`

Examples
===

**Sets**
  - Objects: Sets
  - Morphisms: Functions

**Vector Spaces**
  - Objects: Things like `ℝⁿ` with additionm scalar multiplication
  - Morphisms: Linear Transformations

**Contexts** (as in Lean's Info View)
  - Objects: Sets of assignments of variables to types
  - Moprhisms: Substitutions

Example: The Category of Directed Graphs
===

In Lean, a simple directed graph class is defined by. -/

class Graph.{u} where
  V : Type u
  E : V → V → Prop

namespace Graph


/-

Here are two small graphs, for example.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQzWTtwjv7QALi-tC3RV_1lXZExyuMWckx4DGkuhzZu_9OSmD2ZldukzPPxVdtYwuJD3_tYLFh8gyrR/pub?w=695&amp;h=209" height=20% ⟩

Let's show that the `Graph` type is a Category. -/


/-
Example: Graph Morphisms
===

Every category has a different notion of what a morphism is.

For Graphs, a morphism relating two graphs `G` and `H` is required to preserve
the edge relationship.  -/

@[ext]
structure Hom (G H : Graph) where
  f : G.V → H.V
  pe: ∀ x y, G.E x y → H.E (f x) (f y)

/- With the notion of a `Graph` morphism defined, we can instantiate the `quiver` class, which
allows us to write `G ⟶ H` for our morphisms. -/

instance inst_quiver : Quiver Graph := ⟨
  fun G H => Hom G H
⟩

/- In Lean, the class `Category` extends the class `Quiver`.


Example: A Morphism Between Two Graphs
===

As an example, here are two graphs:


<img src="https://docs.google.com/drawings/d/e/2PACX-1vQPk2cl9FCCrOcGcwbIJtqL_-lP-d20u6wWSJEZhAsc6EwopVkNBU2sjAmJJZwkj7nXZb8RU4cQoc4H/pub?w=1440&amp;h=1080" height=20% ⟩

Suppose we have a function `f : V₁ → V₂` sending 0 ↦ 0 and 0 ↦ 1.
We check that `f` is a morphism:

  - 0 → 1     ⟹     f(0) → f(1)    ≡      0 → 0       ✅
  - 1 → 0     ⟹     f(1) → f(0)    ≡      0 → 0       ✅

In Lean:
-/

def G : Graph := ⟨ Fin 2, fun x y => x = y+1 ∨ y = x+1 ⟩
def H : Graph := ⟨ Fin 1, fun _ _ => True ⟩

def f : G ⟶ H := ⟨ fun v => ⟨ 0, Nat.one_pos ⟩, by
    intro x y h
    simp_all[G,H]
  ⟩

/-
Example: Identity and Composition on Graphs
===

To instantiate Graph as a Category, we need and id morphism, and composition. -/

def id_hom (G : Graph) : Hom G G := ⟨ fun x => x, fun _ _ h => h ⟩

def comp_hom {G H I : Graph} (φ : G ⟶ H) (ψ : H ⟶ I) : Hom G I :=
  ⟨
    ψ.f ∘ φ.f,
    by
      intro x y h
      exact ψ.pe (φ.f x) (φ.f y) (φ.pe x y h)
  ⟩

/-
Example: Graphs Form a Category
===

Showing graphs are a category is now easy. -/

instance inst_category : Category Graph := {
  id := id_hom,
  comp := comp_hom,
  id_comp := by aesop,
  comp_id := by aesop,
  assoc := by aesop
}

/-
Notation for Morphisms
===

The `Category` instances allows us to use the notation `𝟙 G` and `≫`.

Note: `f ≫ g` means apply `f`, then apply `g`. It is notation for `comp g f`. -/

example : (𝟙 G) ≫ f = f := by rfl
example : f ≫ (𝟙 H) = f := by rfl
example : ((𝟙 G) ≫ f) ≫ (𝟙 H) = (𝟙 G) ≫ (f ≫ (𝟙 H)) := by rfl

end Graph

/-

Category Theory: Binary Products
===

A binary product of two objects `X₁` and `X₂` in a category is an object called `X₁ × X₂`. We need
projections and a universal property:

> For every object `Y` and morphisms `f₁ : Y ⟶ X₁`
> and `f₂ : Y ⟶ X₂` there is a unique morphism `f : Y ⟶ X₁ × X₂` such that
> `f ≫ π₁ = f₁` and `f ≫ π₂ = f₂`.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQPk2cl9FCCrOcGcwbIJtqL_-lP-d20u6wWSJEZhAsc6EwopVkNBU2sjAmJJZwkj7nXZb8RU4cQoc4H/pub?w=960&amp;h=720" height=50%>

Binary Products in Lean
===

We call the unique morphism `pair`. The properties `pairᵢ` record the
above universal property, and the `unique_pair` property records the requirement
the morphism is unique. -/

@[ext]
class HasProduct.{u} (C : Type u) [Category C] where

  prod : C → C → C
  π₁ {X₁ X₂ : C} : (prod X₁ X₂) ⟶ X₁
  π₂ {X₁ X₂ : C} : (prod X₁ X₂) ⟶ X₂

  pair {X₁ X₂ Y : C} (_ : Y ⟶ X₁) (_ : Y ⟶ X₂) : Y ⟶ (prod X₁ X₂)
  pair₁ {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) : pair f₁ f₂ ≫ π₁ = f₁
  pair₂ {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) : pair f₁ f₂ ≫ π₂ = f₂
  pair_unique {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (h : Y ⟶ prod X₁ X₂)
    (h_comm₁ : h ≫ π₁ = f₁) (h_comm₂ : h ≫ π₂ = f₂) : h = pair f₁ f₂

namespace HasProduct

/-
Product Notation
===
-/

instance inst_hmul {C : Type*} [Category C] [HasProduct C] : HMul C C C where
  hMul := prod

example {C : Type*} [Category C] [HasProduct C] (A B : C) : A*B = A*B := by sorry

/-
Pairs of Morphisms
===

Pair only describes how to take the product of morphisms with the same domain.
The following method, which builds on `pair`, allows products of arbitary morphisms,
which will be useful in defining exponentials later.  -/

def prod_map.{u} {C : Type u} [Category C] [HasProduct C]
             {X₁ Y₁ X₂ Y₂ : C} (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
  : (prod Y₁ Y₂) ⟶ (prod X₁ X₂) :=
  let P := prod Y₁ Y₂
  let g₁ : P ⟶ X₁ := π₁ ≫ f₁
  let g₂ : P ⟶ X₂ := π₂ ≫ f₂
  pair g₁ g₂

/-
Notation for Pairs of Morphisms
===

-/

instance inst_hmul_morph {C : Type*} [Category C] [HasProduct C] {Y₁ X₁ Y₂ X₂ : C} :
         HMul (Y₁ ⟶ X₁) (Y₂ ⟶ X₂) ((prod Y₁ Y₂) ⟶ (prod X₁ X₂)) where
  hMul := prod_map

namespace Temp

variable (C : Type*) [Category C] [HasProduct C] (X Y : C) (f g : X ⟶ Y)
#check f * g
#check π₁ ≫ f * g ≫ 𝟙 Y

end Temp

/-
Example: Graphs Have Products
===

Graphs have products called Tensor Products, which we can use to instantiate the `HasProduct` class.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vS8m1ASMsZn0P7p6k0rOGj-8KKBhahoNL7SvrASBquIOwZdxX3_t_49JfFJ7WtowCD-AvSfSe1vkldt/pub?w=814&amp;h=368" height=30% \>

-/

def TensorProd (G H : Graph) : Graph := {
  V := G.V × H.V,
  E := fun (u1,v1) (u2,v2) => G.E u1 u2 ∧ H.E v1 v2
}

namespace TensorProd

/-
Example: Tensor Product Properties
===

To form an insstance of a `HasProduct` It will be convenient to have the following
properties defined as theorems.

-/

theorem left {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → G.E x.1 y.1 := by
  intro x y h
  exact h.left

theorem right {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → H.E x.2 y.2 := by
  intro x y h
  exact h.right

end TensorProd

/-
Example: Graphs Have Products
===

Now we can instantiate the `HasProduct` class for graphs.

-/

instance Graph.inst_has_product : HasProduct Graph := {
  prod := TensorProd,
  π₁ := fun {X₁ X₂ : Graph} => ⟨ Prod.fst, TensorProd.left ⟩,
  π₂ := fun {X₁ X₂ : Graph} => ⟨ Prod.snd, TensorProd.right⟩,
  pair := fun {X Y Z} f₁ f₂ => ⟨ fun z => ( f₁.f z, f₂.f z ), by
      intro x y h
      exact ⟨ f₁.pe x y h, f₂.pe x y h ⟩
    ⟩
  pair₁ := by intros; rfl
  pair₂ := by intros; rfl
  pair_unique := by
    intro _ _ _ _ _ _ h1 h2
    rw[←h1,←h2]
    rfl

}

end HasProduct


/-
Category Theory: Exponentials
===

The Exponential Object Z^Y in many cases can be thought of all functions from
Y into Z. We need an evaluation function

  eval : Z^Y × Y → Z

which takes a function in Z^Y and applies it to Y to get an element of Z.

We also need a univeral property, which states that for any X and morphism
g : X × Y → Z there is a unique morphism λg : X → Z^Y so that (λg × (𝟙 Y)) ≫ eval = g.

  X × Y -- λg×(𝟙 Y) --> Z^Y × Y  --eval--> Z
    |                                      ∧
    |                                      |
    +-------------------g------------------+

This basically says that any morphism from X × Y to Z has the form
(λg × (𝟙 Y)) ≫ eval. There isn't a simpler way to say it.

Typically, one defines a curry function so that

  X × Y ⟶ Z  ---curry---> X ⟶ Z^Y

so that λg = curry g × 𝟙 Y.

HasExp
===

Here's the implementation
-/

open HasProduct in
class HasExp.{u,v} (C : Type u) [Category.{v} C] [HasProduct.{u} C] where

  exp : C → C → C
  eval {Z Y : C} : (prod (exp Z Y) Y) ⟶ Z
  curry {X Y Z : C} (g : (prod X Y) ⟶ Z) : X ⟶ (exp Z Y)

  curry_eval {X Y Z : C} (g : prod X Y ⟶ Z)
    : prod_map (curry g) (𝟙 Y) ≫ eval = g

  curry_unique {X Y Z : C} (g : X ⟶ exp Z Y) (h : prod X Y ⟶ Z)
    (comm : prod_map g (𝟙 Y) ≫ eval = h)
    : curry h = g

namespace HasExp

#check HasExp

instance inst_hpow.{u, v} {C : Type u} [Category.{v} C]
         [HasProduct.{u} C] [HasExp.{u, v} C]
  : HPow C C C where
  hPow := exp

instance inst_pow.{u, v} {C : Type u} [Category.{v} C]
         [HasProduct.{u} C] [HasExp.{u, v} C] : Pow C C where
  pow := exp

def uncurry.{u,v} {C : Type u} [Category.{v} C] [HasProduct.{u} C]
    (A B Z : C) [HasExp C] (g : Z ⟶ B ^ A) := (g * (𝟙 A)) ≫ eval

/-
Products distribute over sums: \(A\times (B+C)\cong (A\times B)+(A\times C)\)
 (using categorical coproducts, which generalize disjoint union).
 Exponents convert sums to products: \(B^{(A+C)}\cong B^{A}\times B^{C}\).
 Exponents of exponents multiply: \((C^{B})^{A}\cong C^{(B\times A)}\).  -/

def thing.{u,v} (C : Type u) [Category.{v} C] [HasProduct.{u} C] [HasExp.{u,v} C] (X Y Z : C)
       : Iso ((X^Y)^Z) (X^(Y*Z)) := by
    let f1 := 𝟙 ((X^Y)^Z)
    let f2 := uncurry f1

    sorry

end HasExp

end LeanW26
