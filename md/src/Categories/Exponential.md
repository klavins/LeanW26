
Category Theory: Exponentials
===

<img src="https://docs.google.com/drawings/d/e/2PACX-1vRE5Mmfx10f5A0c9oc94fXmYx0f5sEf4U-wh0c_esWBV02gyE0rMPcf1BBaZ5aoARFXBpSNp-S2uWh1/pub?w=1440&amp;h=1080" width=60%>

The Exponential Object Z^Y in many cases can be thought of all functions from
Y into Z. We need an evaluation function

```lean
  eval : Z^Y × Y → Z
```
and a univeral property, which states that for any X and morphism
g : X × Y → Z there is a unique morphism λg : X → Z^Y so that (λg × (𝟙 Y)) ≫ eval = g.



Currying
===

Currying (after the logician Haskell Curry, 1900-1982) is a way to take a function of two
arguments and combine it into two functions of one argument.

For example suppose `f = fun x y => x+y`. Then `f x = fun y => x+y`.

Here `f : X*Y → Z` and `f x : Y → Z`. The operation that does this is called `curry`,
which is an operation on functions:

```
    curry : (X*Y → Z) → (X → (Y → Z))
```

or in the notation of Category theory

```
    curry : (X*Y ⟶ Z) → (X ⟶ Z^Y)
```

Currying in a Category
===

<img src="https://docs.google.com/drawings/d/e/2PACX-1vRE5Mmfx10f5A0c9oc94fXmYx0f5sEf4U-wh0c_esWBV02gyE0rMPcf1BBaZ5aoARFXBpSNp-S2uWh1/pub?w=1440&amp;h=1080" width=60%>

So `curry` to has type:

```lean
curry : (X × Y ⟶ Z) → (X ⟶ Z^Y)
```

So

```lean
curry g : X ⟶ Z^Y            and            λg = curry g × 𝟙 Y
```



HasExp
===

Here's the implementation

```lean
open HasProduct in
class HasExp.{u,v} (C : Type u) [Category.{v} C] [HasProduct.{u} C] where

  exp : C → C → C
  eval {Z Y : C} : (prod (exp Z Y) Y) ⟶ Z
  curry {X Y Z : C} (g : (prod X Y) ⟶ Z) : X ⟶ (exp Z Y)

  curry_eval {X Y Z : C} (g : prod X Y ⟶ Z)
    : ‹curry g, 𝟙 Y› ≫ eval = g

  curry_unique {X Y Z : C} (g : X ⟶ exp Z Y)
    : curry ( ‹g, 𝟙 Y› ≫ eval) = g
```

Notation Class Instances
===

```lean
instance HasExp.inst_hpow.{u, v} {C : Type u} [Category.{v} C]
         [HasProduct.{u} C] [HasExp.{u, v} C]
  : HPow C C C where
  hPow := exp

instance HasExp.inst_pow.{u, v} {C : Type u} [Category.{v} C]
         [HasProduct.{u} C] [HasExp.{u, v} C] : Pow C C where
  pow := exp
```
 Now we can write: 
```lean
universe u v
variable {C : Type u} [Category.{v} C] [HasProduct.{u, v} C] [HasExp.{u, v} C]
variable {X Y Z S A V : C}

#check (X^Y)*Z
```

Beta Reduction = `curry_eval`
===
Rewrite HasExp properties so they can be used with simp. 
```lean
open HasProduct HasExp in
@[simp, reassoc]
theorem beta {f : X * Y ⟶ Z}
  : ‹curry f, 𝟙 Y› ≫ eval = f := by
    apply curry_eval

open HasProduct HasExp in
@[simp, reassoc]
theorem beta_alt {f : X * Y ⟶ Z}
  : (pair (π₁ ≫ curry f) (π₂ ≫ (𝟙 Y))) ≫ eval = f := by
    apply curry_eval
```

Eta Reduction = `curry_unique`
===

```lean
open HasProduct HasExp in
@[simp, reassoc]
theorem eta {g : X ⟶ exp Z Y}
  : curry ( ‹g, 𝟙 Y› ≫ eval ) = g := by
    apply curry_unique

open HasProduct HasExp in
@[simp, reassoc]
theorem eta_alt {g : X ⟶ exp Z Y}
  : curry ( pair (π₁ ≫ g) (π₂ ≫ (𝟙 Y)) ≫ eval ) = g := by
    apply curry_unique
```

Extensionality
===

These theorems state that if two functions evaluate to the same thing on their arguments,
then they are the same.

```lean
open HasProduct HasExp in
lemma exp_ext {f g : X ⟶ (Z ^ Y)} :
  ‹f,  𝟙 Y› ≫ eval = ‹g,  𝟙 Y› ≫ eval → f = g := by
    intro hyp
    apply congrArg curry at hyp
    rw[eta,eta] at hyp
    exact hyp

open HasProduct HasExp in
lemma exp_ext_alt {f g : X ⟶ (Z ^ Y)} :
  pair (π₁ ≫ f) (π₂ ≫ 𝟙 Y) ≫ eval = pair (π₁ ≫ g) (π₂ ≫ 𝟙 Y) ≫ eval → f = g := by
    intro hyp
    apply congrArg curry at hyp
    rw[eta_alt,eta_alt] at hyp
    exact hyp
```

Uncurrying
===

```lean
def HasExp.uncurry (g : X ⟶ Z ^ Y) : X * Y ⟶ Z :=   ‹g, 𝟙 Y›  ≫ HasExp.eval

open HasProduct HasExp in
theorem curry_uncurry (g : X * Y ⟶ Z)
  : uncurry (curry g) = g := by apply curry_eval

open HasProduct HasExp in
theorem uncurry_curry (g : X ⟶ Z ^ Y)
  : curry (uncurry g) = g := by apply curry_unique

open HasProduct HasExp in
theorem uncurry_both_sides {f g : X ⟶ Z ^ Y}
  : f = g ↔ (uncurry f = uncurry g) := by
  constructor
  · intro h
    rw[h]
  · intro h
    apply congrArg curry at h
    simp[uncurry_curry] at h
    exact h
```

Sliding
===

```lean
open HasProduct HasExp in
@[simp, reassoc]
theorem sliding {m : S ⟶ A} {n : X ⟶ V} {h : A * V ⟶ X}
    : ‹m ≫ curry h, n› ≫ eval =  ‹m, n› ≫ h := by
    have : n = n ≫ (𝟙 V) := Eq.symm (Category.comp_id n)
    rw[this]
    rw[prod_map_comp]
    rw[Category.assoc]
    rw[←this]
    have : ‹curry h, 𝟙 V› ≫ HasExp.eval = h := by
      apply curry_eval
    rw[this]
```

Associativity
===

```lean
open HasProduct HasExp in
theorem exp_prod : ∃ f : Iso ((X^Y)^Z) (X^(Y*Z)), True := by

    let F : ((X^Y)^Z)*(Y*Z) ⟶ X :=
        pair (‹ 𝟙 ((X ^ Y) ^ Z), π₂ › ≫ eval) (π₂ ≫ π₁) ≫ eval

    let f : (X^Y)^Z ⟶ X^(Y*Z) :=
        curry F

    let G : (X^(Y*Z)*Z)*Y ⟶ X :=
        pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ eval

    let g : X^(Y*Z) ⟶ (X^Y)^Z :=
        curry (curry G)

    use ⟨
      f,
      g,
      by
        simp[f,g]

        sorry,
      by
        simp[f,g]
        sorry
    ⟩
```

Example: Reflexive Graphs: A Subcategory of Graphs
===

To show an example of exponentials, we can't use simple graphs, as we need self-loops (Why?)
We can build a subcategory of Graph called ReflexiveGraph that does this using
Mathlib's `FullSubcategory` helper. 
```lean
def ReflexiveGraph : Type (u+1) :=
  ObjectProperty.FullSubcategory (fun G : Graph.{u} => ∀ v, G.E v v)

--hide
namespace ReflexiveGraph
--unhide
```
 We can then show ReflexiveGraph is also a category and that it has products. 
```lean
instance inst_category : Category ReflexiveGraph.{u} :=
  ObjectProperty.FullSubcategory.category _
```

Products in Reflexive Graphs
===

For the product instance, it would be nice if there were a way to just use the
fact that Graphs have products. Or at least use some of that proof. But I could not
figure that out so this is mostly just repetetive at this point. 
```lean
open HasProduct in
instance inst_has_product : HasProduct.{u+1} ReflexiveGraph.{u} := {

  prod := fun G H => ⟨ TensorProd G.1 H.1, fun v => ⟨ G.property v.1, H.property v.2 ⟩ ⟩,
  π₁ := fun {X₁ X₂ : ReflexiveGraph} => Graph.inst_has_product.π₁,
  π₂ := fun {X₁ X₂ : ReflexiveGraph} => Graph.inst_has_product.π₂,

  pair := fun {X₁ X₂ Y : ReflexiveGraph} => fun f₁ f₂ => ⟨ fun y => ( f₁.f y, f₂.f y ), by
    intro x y h
    exact ⟨ f₁.pe x y h, f₂.pe x y h ⟩
  ⟩,

  pair₁ := by intros; rfl,

  pair₂ := by intros; rfl,

  pair_unique {X₁ X₂ Y} := by
    intro h
    rfl

}
```

Reflexive Graphs Have Exponentials
===

Here's a paper with something like this construction:

  https://arxiv.org/pdf/1807.09345

The exponential G^H is the graph in which the vertices are morphisms from H to G,
and the edges are the "natural transformations". The transformation maps vertices
and edges of G to those of H in a way that commutes.

HasExp Instantiation
===

First we define the exponential object of two Reflexive Graphs. Note the universe
condition. We need to have the exponential object like in a higher universe
otherwise we get Russel's paradox issues.

The vertices of the exponential objects G^H are the morphisms from H to G.

If F₁ and F₂ are both morphisms from H to G, there is an edge from
F₁ to F₂ if for all edges x y in H there is an edge from F₁(x) to F₂(x) in G.


```lean
def exp (G H : ReflexiveGraph.{u}) : ReflexiveGraph.{u} := {
  obj := {
    V := ULift.{u} (H ⟶ G),
    E := fun F₁ F₂ =>
      let ⟨ f₁, _ ⟩ := ULift.down F₁ -- function underlying first morphism
      let ⟨ f₂, _ ⟩ := ULift.down F₂ -- function underlying second morphism
      let ⟨ ⟨ hV, hE ⟩, _ ⟩ := H     -- vertices and edges of H
      let ⟨ ⟨ _, gE ⟩, _ ⟩ := G      -- edges of G
      ∀ x y : hV, hE x y → gE (f₁ x) (f₂ y)
  },
  property := by
    intro morphism u v h
    exact morphism.down.pe u v h
}
```

The eval Function is straighforward
===

```lean
def eval (H G : ReflexiveGraph) : HasProduct.prod (exp H G) G ⟶ H := {
    f := fun ⟨ ⟨ f, h ⟩, v  ⟩ => f v,
    pe := by
      intro ⟨ ⟨ fg, hfg ⟩, vG ⟩ ⟨ ⟨ fh, hfh ⟩, fH ⟩ ⟨ h1, h2 ⟩
      simp_all only[exp]
      exact h1 vG fH h2
}
```

Instantiating HasExp
===

```lean
instance inst_has_exp : HasExp ReflexiveGraph := {

  exp := exp,
  eval := fun {G H} => eval G H,

  curry := fun {X Y Z} => fun ⟨ f, h ⟩ => ⟨ fun x => ⟨ fun y => f (x,y), by
      intro _ _ e
      apply h
      exact ⟨ X.property x, e ⟩
     ⟩, by
        intros _ _ ex _ _ ey
        apply h
        exact ⟨ex, ey⟩
    ⟩

  curry_eval := by intros; rfl,

  curry_unique := by
    intro X Y A g
    rfl

}
```
 Hooray! 
```lean
--hide
end ReflexiveGraph
--unhide

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

