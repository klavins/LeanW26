import Mathlib
import LeanW26.Categories.Category
import LeanW26.Categories.BinaryProduct

namespace LeanW26

open CategoryTheory


/-
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

Currying in a Category
===

<img src="https://docs.google.com/drawings/d/e/2PACX-1vRE5Mmfx10f5A0c9oc94fXmYx0f5sEf4U-wh0c_esWBV02gyE0rMPcf1BBaZ5aoARFXBpSNp-S2uWh1/pub?w=1440&amp;h=1080" width=60%>

We define `curry` to have type:

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


/-
Notation Class Instances
===
-/

instance HasExp.inst_hpow.{u, v} {C : Type u} [Category.{v} C]
         [HasProduct.{u} C] [HasExp.{u, v} C]
  : HPow C C C where
  hPow := exp

instance HasExp.inst_pow.{u, v} {C : Type u} [Category.{v} C]
         [HasProduct.{u} C] [HasExp.{u, v} C] : Pow C C where
  pow := exp

/- Now we can write: -/


namespace Temp

variable (C : Type*) [Category C] [HasProduct C] [HasExp C] (X Y Z : C)
#check (X^Y)*Z

end Temp


/-
Reflexive Graphs: A Subcategory of Graphs
===

To show an example of exponentials, we can't use simple graphs, as we need self-loops (Why?)
We can build a subcategory of Graph called ReflexiveGraph that does this using
Mathlib's `FullSubcategory` helper. -/


def ReflexiveGraph.{u} : Type (u+1) :=
  ObjectProperty.FullSubcategory (fun G : Graph.{u} => ∀ v, G.E v v)

--hide
namespace ReflexiveGraph
--unhide

/- We can then show ReflexiveGraph is also a category and that it has products. -/

instance inst_category.{u} : Category ReflexiveGraph.{u} :=
  ObjectProperty.FullSubcategory.category _

/-
Products in Reflexive Graphs
===

For the product instance, it would be nice if there were a way to just use the
fact that Graphs have products. Or at least use some of that proof. But I could not
figure that out so this is mostly just repetetive at this point. -/

--hide
open HasProduct
--unhide

instance inst_has_product.{u} : HasProduct.{u+1} ReflexiveGraph.{u} := {

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
    intro _ _ _ h1 h2
    simp[←h1,←h2]
    rfl

}

/-
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

-/

def exp.{u} (G H : ReflexiveGraph.{u}) : ReflexiveGraph.{u} := {
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

/-
The eval Function is straighforward
===
-/

def eval (H G : ReflexiveGraph) : HasProduct.prod (exp H G) G ⟶ H := {
    f := fun ⟨ ⟨ f, h ⟩, v  ⟩ => f v,
    pe := by
      intro ⟨ ⟨ fg, hfg ⟩, vG ⟩ ⟨ ⟨ fh, hfh ⟩, fH ⟩ ⟨ h1, h2 ⟩
      simp_all only[exp]
      exact h1 vG fH h2
}

/-
Instantiating HasExp
===
-/

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
    intro _ _ _ _ _ comm
    rw[←comm]
    rfl

}

/- Hooray! -/

--hide
end ReflexiveGraph
--unhide


/-
Uncurrying
===
-/

def HasExp.uncurry.{u,v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C] [HasExp.{u, v} C]
  {X Y Z : C} (g : X ⟶ Z ^ Y) : X * Y ⟶ Z := (g * (𝟙 Y)) ≫ eval

open HasProduct HasExp in
theorem curry_uncurry.{u, v} {C : Type u}
   [Category.{v} C] [HP : HasProduct.{u, v} C] [HE : HasExp.{u, v} C]
   (X Y Z : C) (g : X * Y ⟶ Z)
  : uncurry (curry g) = g := by
    unfold uncurry
    apply curry_eval

/-
An Example Theorem
===
-/

/-
 - prod_map (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) : (prod Y₁ Y₂) ⟶ (prod X₁ X₂)
 - curry (g : (prod X Y) ⟶ Z) : X ⟶ (exp Z Y)
 - uncurry (g : X ⟶ Z ^ Y) : X * Y ⟶ Z
-/

open HasProduct in
@[simp]
def prod_swap.{u, v} {C : Type u} (X Y : C) [Category.{v} C] [HasProduct.{u, v} C]
   : X * Y ⟶ Y * X := pair π₂ π₁


open HasProduct HasExp in
theorem exp_prod.{u, v} (C : Type u) [Category.{v} C] [HasProduct.{u, v} C] [HasExp.{u, v} C]
    (X Y Z : C) : ∃ f : Iso ((X^Y)^Z) (X^(Y*Z)), True := by

    let f1 : (X^Y)^Z ⟶ X^(Y*Z) :=
        curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ eval) (π₂ ≫ π₁) ≫ eval)

    let f2 : X^(Y*Z) ⟶ (X^Y)^Z :=
        curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ eval))

    use ⟨
      f1,
      f2,
      by
        unfold f1 f2
        simp[prod_map,Category.comp_id]

        sorry,
      by
        unfold f1
        unfold f2

        sorry
    ⟩


    -- let f1' : (X^Y)^Z ⟶ X^(Y*Z) :=
    --    let E := (X^Y)^Z
    --    let ev1 : E * Z ⟶ X ^ Y := eval (Z := exp X Y) (Y := Z)
    --    let evXY :  (X^Y) * Y ⟶ X := eval (Z := X) (Y := Y)
    --    let projZ_from_pair : E* (Y * Z) ⟶ E * Z := prod_map (𝟙 E) (π₂ : Y * Z ⟶ Z)
    --    let to_expX_Y : E * (Y * Z) ⟶ X ^ Y :=  projZ_from_pair ≫ ev1
    --    let projY_from_pair : E * (Y * Z) ⟶ Y :=
    --        (π₂ : E * (Y * Z) ⟶ Y * Z) ≫ (π₁ : Y * Z ⟶ Y)
    --    let body : E * (Y * Z) ⟶ X := pair to_expX_Y projY_from_pair ≫ evXY
    --    curry body


    -- let f2' : X^(Y*Z) ⟶ (X^Y)^Z :=
    --     let E := X ^ (Y * Z)
    --     let evYZ : E * (Y * Z) ⟶ X := eval (Z := X) (Y := Y * Z)
    --     let projE : (E * Z) * Y ⟶ E := π₁ ≫ π₁
    --     let projZ : (E * Z) * Y ⟶ Z := π₁ ≫ π₂
    --     let projY : (E * Z) * Y ⟶ Y :=  π₂
    --     let yz : (E * Z) * Y ⟶ Y * Z := pair projY projZ
    --     let body : (E * Z) * Y ⟶ X := pair (projE) (yz) ≫ evYZ
    --     curry (curry body)

--hide
end LeanW26
--unhide
