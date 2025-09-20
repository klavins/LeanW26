
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
  - Objects: Things like `ℝⁿ` with addition and scalar multiplication
  - Morphisms: Linear Transformations

**Contexts** (as in Lean's Info View)
  - Objects: Sets of assignments of variables to types
  - Moprhisms: Substitutions

Example: The Category of Directed Graphs
===

In Lean, a simple directed graph class is defined by. 
```lean
class Graph.{u} where
  V : Type u
  E : V → V → Prop

--hide
namespace Graph
--unhide
```


Here are two small graphs, for example.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQzWTtwjv7QALi-tC3RV_1lXZExyuMWckx4DGkuhzZu_9OSmD2ZldukzPPxVdtYwuJD3_tYLFh8gyrR/pub?w=695&amp;h=209" height=20% >

Let's show that the `Graph` type is a Category. 

Example: Graph Morphisms
===

Every category has a different notion of what a morphism is. For Graphs, a morphism
relating two graphs `G` and `H` is required to preserve the edge relationship.  
```lean
@[ext]
structure Hom (G H : Graph) where
  f : G.V → H.V
  pe: ∀ x y, G.E x y → H.E (f x) (f y)
```
 With the notion of a `Graph` morphism defined, we can instantiate the `quiver` class, which
allows us to write `G ⟶ H` for our morphisms. 
```lean
instance inst_quiver : Quiver Graph := ⟨
  fun G H => Hom G H
⟩
```
 In Lean, the class `Category` extends the class `Quiver`.


Example: A Morphism Between Two Graphs!
===

As an example, here are two graphs:

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQzWTtwjv7QALi-tC3RV_1lXZExyuMWckx4DGkuhzZu_9OSmD2ZldukzPPxVdtYwuJD3_tYLFh8gyrR/pub?w=695&amp;h=209" height=20%>

Suppose we have a function `f : V₁ → V₂` sending 0 ↦ 0 and 0 ↦ 1.
We check that `f` is a morphism:

  - 0 → 1     ⟹     f(0) → f(1)    ≡      0 → 0       ✅
  - 1 → 0     ⟹     f(1) → f(0)    ≡      0 → 0       ✅

Example: Example Graph Morphism in Lean
===

```lean
def G : Graph := ⟨ Fin 2, fun x y => x = y+1 ∨ y = x+1 ⟩
def H : Graph := ⟨ Fin 1, fun _ _ => True ⟩

def f : G ⟶ H := ⟨ fun v => ⟨ 0, Nat.one_pos ⟩, by
    intro x y h
    simp_all[G,H]
  ⟩
```

Example: Identity and Composition on Graphs
===

To instantiate Graph as a Category, we need and id morphism, and composition. 
```lean
def id_hom (G : Graph) : Hom G G := ⟨ fun x => x, fun _ _ h => h ⟩

def comp_hom {G H I : Graph} (φ : G ⟶ H) (ψ : H ⟶ I) : Hom G I :=
  ⟨
    ψ.f ∘ φ.f,
    by
      intro x y h
      exact ψ.pe (φ.f x) (φ.f y) (φ.pe x y h)
  ⟩
```

Example: Graphs Form a Category
===

Showing graphs are a category is now easy. 
```lean
instance inst_category : Category Graph := {
  id := id_hom,
  comp := comp_hom,
  id_comp := by aesop,
  comp_id := by aesop,
  assoc := by aesop
}
```

Notation for Morphisms
===

The `Category` instances allows us to use the notation `𝟙 G` and `≫`.

Note: `f ≫ g` means apply `f`, then apply `g`. It is notation for `comp g f`. 
```lean
example : (𝟙 G) ≫ f = f := by rfl
example : f ≫ (𝟙 H) = f := by rfl
example : ((𝟙 G) ≫ f) ≫ (𝟙 H) = (𝟙 G) ≫ (f ≫ (𝟙 H)) := by rfl

--hide
end Graph
--unhide
```

Exercises
===

1. Define an inductive type `BinTree` to represent binary trees.
1. Show that `BinTree` forms a Category, using the same notion of morphism as we used for `Graph`.
1. Redo the above using Mathlib's `Fullsubcatgory` definition to define a new type `BinTree'`
   as a subcategory of `Graph`.


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

