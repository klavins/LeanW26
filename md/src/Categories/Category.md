
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

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQzWTtwjv7QALi-tC3RV_1lXZExyuMWckx4DGkuhzZu_9OSmD2ZldukzPPxVdtYwuJD3_tYLFh8gyrR/pub?w=695&amp;h=209" width=40% >

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

Example: Graph Quivers
===

With the notion of a `Graph` morphism defined, we can instantiate
the `quiver` class, which allows us to write `G ⟶ H` for our morphisms. 
```lean
instance inst_quiver : Quiver Graph := ⟨
  fun G H => Hom G H
⟩

@[ext]
lemma Hom.ext_helper {G H : Graph} (f g : G ⟶ H) (h : f.f = g.f) : f = g := by
  simp[Graph.inst_quiver] at f g
  cases f; cases g
  simp_all
```
 In Lean, the class `Category` extends the class `Quiver`.

Example: A Graph Morphism
===

As an example, here are two graphs:

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQzWTtwjv7QALi-tC3RV_1lXZExyuMWckx4DGkuhzZu_9OSmD2ZldukzPPxVdtYwuJD3_tYLFh8gyrR/pub?w=695&amp;h=209" width=40%>

Suppose we have a function `f : V₁ → V₂` sending 0 ↦ 0 and 0 ↦ 1.
We check that `f` is a morphism:

  - 0 → 1     ⟹     f(0) → f(1)    ≡      0 → 0       ✅
  - 1 → 0     ⟹     f(1) → f(0)    ≡      0 → 0       ✅

Example: A Graph Morphism in Lean
===

```lean
def G : Graph := ⟨ Fin 2, fun x y => x = y+1 ∨ y = x+1 ⟩
def H : Graph := ⟨ Fin 1, fun _ _ => True ⟩

def f : G ⟶ H := ⟨ fun v => ⟨ 0, Nat.one_pos ⟩, by
    intro x y h
    simp_all[G,H]
  ⟩
```

Example: Identity and Composition
===

To instantiate Graph as a Category, we need and id morphism, and composition. 
```lean
def id_hom (G : Graph) : G ⟶ G := ⟨ fun x => x, fun _ _ h => h ⟩

def comp_hom {G H I : Graph} (φ : G ⟶ H) (ψ : H ⟶ I) : G ⟶ I :=
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

Isomorphisms
===

An isomorphism in a category `C` is a morphism `f : A ⟶ B` such that there exists
a morphism `g : B ⟶ A` with `f ≫ g = 𝟙 A`. In the category Graph, a simple example
is a function that relabels vertices.

```lean
def relabel (G : Graph) (r : G.V ≃ G.V) : Graph := ⟨
  G.V,
  fun x y => G.E (r.symm x) (r.symm y)
⟩
```
 Here,
- `≃` means bijection
- `r.symm` is the inverse of r (technicly an `Equiv`).  

Example: The `relabel` isomorphism
===

We can define an Isomorphism from `relabel` as follows: 
```lean
def relabel_iso (G : Graph) (r : G.V ≃ G.V)
  : Iso G (relabel G r) := ⟨
    ⟨ r.toFun, by intro x y he
                  simp[relabel,he] ⟩,
    ⟨ r.invFun, by intro x y he
                   exact he ⟩,
    by ext
       simp[Graph.inst_category,Graph.comp_hom,Graph.id_hom],
    by ext
       simp[Graph.inst_category,Graph.comp_hom,Graph.id_hom]
  ⟩
```

Functors
===

A ***Functor*** `F : C ⥤ D` between categories `C` and `D` is a mapping of objects to
objects and morphisms to morphisms such that:

- If `f : A ⟶ B` is a morphism in `C` then `F(f) : F(A) ⟶ F(B)` is the resulting morphism in `D`.
- `F(𝟙 A) = 𝟙 F(A)`
- `F(f ≫ g) = F(f) ≫ F(g)`



Example: The Forgetful Functor
===

The forgetful functor for a category is one that forgets everything except the type of its objects.
Here, we show the forgetful functor for `Graph`. Note that we use the category `Type` which is
instantiated as a Category in Mathlib. 
```lean
def V : Graph ⥤ Type := {
  obj G := G.V,
  map {G H} f := f.f
}
```
 Note that the fields `map_id` and `map_comp` are discharged by the default proof
for the Functor class, which is `cat_disch`, so we don't need to prove them for simple cases.  

Example: The Id Endofunctor
===

```lean
def Graph.id : Graph ⥤ Graph := {
  obj G := G,
  map {F G} f := f
}
```
 Note: Mathlib defines the identity functor for any category `C` by `𝟭 C`, so
we didn't need to define `Graph.id` and could have written `𝟭 Graph` instead. 

Example: Loop Addition
===

Adding all self loops to a graph is an endofunctor on Graph.


```lean
def Graph.add_loops : Graph ⥤ Graph := {
  obj G := ⟨ G.V, fun x y => x = x ∨ G.E x x ⟩,
  map {F G} f := ⟨ f.f, by simp ⟩
}
```

Example: Relabeling Functor
===

We can elevate relabeling to an endofunctor on Graph as follows.
We define a structure `VertexRelabeling` to contain the data
involved in the relabeling. The property `natural` requires
the relabeling `r` to be consistent across morphisms. 
```lean
structure VertexRelabeling where
  r : ∀ G : Graph, G.V ≃ G.V
  natural : ∀ {G H : Graph} (f : G ⟶ H),
            ∀ x, (r H).symm (f.f x) = f.f ((r G).symm x)

def ReLabel (r : VertexRelabeling) : Graph ⥤ Graph := {
  obj X := relabel X (r.r X),
  map {X Y} f := ⟨ f.f, by
    intro x y he
    simp_all[relabel]
    rw[r.natural f y, r.natural f x]
    apply f.pe
    exact he
   ⟩
}
```

Natural Transformations
===

The requirement that graph relabeling be consistent in order to define a
Functor is a generic issue, which leads to the following definition.

Let `F : C ⥤ D` and `G : C ⥤ D` be morphisms. A ***natural transformation***
`η : F ⇒ G` is a map between functors that
assigns every object `X : D` to a morphism `η_X : F(X) ⟶ G(X)` such that

```lean
F.map f ≫ app Y = app X ≫ G.map f
```

<img src="https://wiki.haskell.org/wikiupload/e/ee/Natural_transformation.png" width=50%></img>



Natural Transormations in Lean
===

In Lean, natural transformations are defined via the structure:

```lean
structure NatTrans (F G : C ⥤ D) where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ {X Y : C} (f : X ⟶ Y),
    F.map f ≫ app Y = app X ≫ G.map f
```

Note that `C ⥤ D` forms a category itself where the objects of the category
are morphisms from `C` to `D` and the morphisms are natural transformations.

Thus, to define a natural transformation you might not use `NatTrans` directly. You do:

```lean
def my_natural_transformation : C ⟶ D := ...
```


Example: Relabeling is Natural
===

```lean
def relabel_nat (r : VertexRelabeling) : 𝟭 Graph ⟶ (ReLabel r) := {
  app := fun G =>
    { f := r.r G,
      pe := by
        intros x y hxy
        dsimp[ReLabel,relabel]
        aesop
    },
  naturality := by -- Warning: AI Generated Proof
    intro X Y f
    ext x
    apply Equiv.injective (r.r Y)
    change (r.r Y) ((r.r Y ∘ f.f) x) = (r.r Y) (f.f ((r.r X) x))
    dsimp [Functor.id, ReLabel, relabel, Functor.comp]
    aesop_cat_nonterminal
    apply (Equiv.apply_eq_iff_eq_symm_apply (r.r Y)).mpr
    simp[r.natural]
}

#check relabel_nat
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

