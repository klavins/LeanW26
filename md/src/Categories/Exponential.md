
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

```lean
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
namespace Temp

variable (C : Type*) [Category C] [HasProduct C] [HasExp C] (X Y Z : C)
#check (X^Y)*Z

end Temp
```

Reflexive Graphs: A Subcategory of Graphs
===

To show an example of exponentials, we can't use simple graphs, as we need self-loops (Why?)
We can build a subcategory of Graph called ReflexiveGraph that does this using
Mathlib's `FullSubcategory` helper. 
```lean
def ReflexiveGraph.{u} : Type (u+1) :=
  ObjectProperty.FullSubcategory (fun G : Graph.{u} => ∀ v, G.E v v)

--hide
namespace ReflexiveGraph
--unhide
```
 We can then show ReflexiveGraph is also a category and that it has products. 
```lean
instance inst_category.{u} : Category ReflexiveGraph.{u} :=
  ObjectProperty.FullSubcategory.category _
```

Products in Reflexive Graphs
===

For the product instance, it would be nice if there were a way to just use the
fact that Graphs have products. Or at least use some of that proof. But I could not
figure that out so this is mostly just repetetive at this point. 
```lean
--hide
open HasProduct
--unhide

instance inst_has_product.{u} : HasProduct.{u+1} ReflexiveGraph.{u} := {

  prod := fun G H => ⟨ TensorProd G.1 H.1, fun v => ⟨ G.property v.1, H.property v.2 ⟩ ⟩,
  π₁ := fun {X₁ X₂ : ReflexiveGraph} => Graph.inst_has_product.π₁,
  π₂ := fun {X₁ X₂ : ReflexiveGraph} => Graph.inst_has_product.π₂,

  pair := fun {X₁ X₂ Y : ReflexiveGraph} => fun f₁ f₂ => ⟨ fun y => ( f₁.f y, f₂.f y ), by <proofstate>['X₁ X₂ Y : ReflexiveGraph\nf₁ : Y ⟶ X₁\nf₂ : Y ⟶ X₂\n⊢ ∀ (x y : Graph.V), Graph.E x y → Graph.E ((fun y ↦ (f₁.f y, f₂.f y)) x) ((fun y ↦ (f₁.f y, f₂.f y)) y)']</proofstate>
    intro x y h <proofstate>['X₁ X₂ Y : ReflexiveGraph\nf₁ : Y ⟶ X₁\nf₂ : Y ⟶ X₂\nx y : Graph.V\nh : Graph.E x y\n⊢ Graph.E ((fun y ↦ (f₁.f y, f₂.f y)) x) ((fun y ↦ (f₁.f y, f₂.f y)) y)']</proofstate>
    exact ⟨ f₁.pe x y h, f₂.pe x y h ⟩
  ⟩,

  pair₁ := by intros; rfl,

  pair₂ := by intros; rfl,

  pair_unique {X₁ X₂ Y} := by <proofstate>['X₁ X₂ Y : ReflexiveGraph\n⊢ ∀ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (h : Y ⟶ { obj := TensorProd X₁.obj X₂.obj, property := ⋯ }),\n    h ≫ π₁ = f₁ → h ≫ π₂ = f₂ → h = { f := fun y ↦ (f₁.f y, f₂.f y), pe := ⋯ }']</proofstate>
    intro _ _ _ h1 h2 <proofstate>['X₁ X₂ Y : ReflexiveGraph\nf₁✝ : Y ⟶ X₁\nf₂✝ : Y ⟶ X₂\nh✝ : Y ⟶ { obj := TensorProd X₁.obj X₂.obj, property := ⋯ }\nh1 : h✝ ≫ π₁ = f₁✝\nh2 : h✝ ≫ π₂ = f₂✝\n⊢ h✝ = { f := fun y ↦ (f₁✝.f y, f₂✝.f y), pe := ⋯ }']</proofstate>
    simp[←h1,←h2] <proofstate>['X₁ X₂ Y : ReflexiveGraph\nf₁✝ : Y ⟶ X₁\nf₂✝ : Y ⟶ X₂\nh✝ : Y ⟶ { obj := TensorProd X₁.obj X₂.obj, property := ⋯ }\nh1 : h✝ ≫ π₁ = f₁✝\nh2 : h✝ ≫ π₂ = f₂✝\n⊢ h✝ = { f := fun y ↦ ((h✝ ≫ π₁).f y, (h✝ ≫ π₂).f y), pe := ⋯ }']</proofstate>
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
  property := by <proofstate>['G H : ReflexiveGraph\n⊢ ∀ (v : Graph.V), Graph.E v v']</proofstate>
    intro morphism u v h <proofstate>['G H : ReflexiveGraph\nmorphism : Graph.V\nu v : Graph.V\nh : Graph.E u v\n⊢ Graph.E (morphism.1.f u) (morphism.1.f v)']</proofstate>
    exact morphism.down.pe u v h
}
```

The eval Function is straighforward
===

```lean
def eval (H G : ReflexiveGraph) : HasProduct.prod (exp H G) G ⟶ H := {
    f := fun ⟨ ⟨ f, h ⟩, v  ⟩ => f v,
    pe := by <proofstate>['H G : ReflexiveGraph\n⊢ ∀ (x y : Graph.V),\n    Graph.E x y →\n      Graph.E\n        (match x with\n        | ({ down := { f := f, pe := h } }, v) => f v)\n        (match y with\n        | ({ down := { f := f, pe := h } }, v) => f v)']</proofstate>
      intro ⟨ ⟨ fg, hfg ⟩, vG ⟩ ⟨ ⟨ fh, hfh ⟩, fH ⟩ ⟨ h1, h2 ⟩ <proofstate>['H G : ReflexiveGraph\nfg : Graph.V → Graph.V\nhfg : ∀ (x y : Graph.V), Graph.E x y → Graph.E (fg x) (fg y)\nvG : Graph.V\nfh : Graph.V → Graph.V\nhfh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (fh x) (fh y)\nfH : Graph.V\nh1 : Graph.E { down := { f := fg, pe := hfg } } { down := { f := fh, pe := hfh } }\nh2 : Graph.E vG fH\n⊢ Graph.E\n    (match ({ down := { f := fg, pe := hfg } }, vG) with\n    | ({ down := { f := f, pe := h } }, v) => f v)\n    (match ({ down := { f := fh, pe := hfh } }, fH) with\n    | ({ down := { f := f, pe := h } }, v) => f v)']</proofstate>
      simp_all only[exp] <proofstate>['H G : ReflexiveGraph\nfg : Graph.V → Graph.V\nhfg : ∀ (x y : Graph.V), Graph.E x y → Graph.E (fg x) (fg y)\nvG : Graph.V\nfh : Graph.V → Graph.V\nhfh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (fh x) (fh y)\nfH : Graph.V\nh1 :\n  match G, { down := { f := fg, pe := hfg } }, { down := { f := fh, pe := hfh } }, fg, ⋯, fh, ⋯ with\n  | { obj := { V := hV, E := hE }, property := property }, F₁, F₂, f₁, pe, f₂, pe_1 =>\n    match H, F₁, F₂, f₁, pe, f₂, pe_1 with\n    | { obj := { V := V, E := gE }, property := property_1 }, F₁, F₂, f₁, pe, f₂, pe_2 =>\n      ∀ (x y : hV), hE x y → gE (f₁ x) (f₂ y)\nh2 : Graph.E vG fH\n⊢ Graph.E (fg vG) (fh fH)']</proofstate>
      exact h1 vG fH h2
}
```

Instantiating HasExp
===

```lean
instance inst_has_exp : HasExp ReflexiveGraph := {

  exp := exp,
  eval := fun {G H} => eval G H,

  curry := fun {X Y Z} => fun ⟨ f, h ⟩ => ⟨ fun x => ⟨ fun y => f (x,y), by <proofstate>['X Y Z : ReflexiveGraph\nx✝ : HasProduct.prod X Y ⟶ Z\nf : Graph.V → Graph.V\nh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (f x) (f y)\nx : Graph.V\n⊢ ∀ (x_1 y : Graph.V), Graph.E x_1 y → Graph.E ((fun y ↦ f (x, y)) x_1) ((fun y ↦ f (x, y)) y)']</proofstate>
      intro _ _ e <proofstate>['X Y Z : ReflexiveGraph\nx✝¹ : HasProduct.prod X Y ⟶ Z\nf : Graph.V → Graph.V\nh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (f x) (f y)\nx : Graph.V\nx✝ y✝ : Graph.V\ne : Graph.E x✝ y✝\n⊢ Graph.E ((fun y ↦ f (x, y)) x✝) ((fun y ↦ f (x, y)) y✝)']</proofstate>
      apply h <proofstate>['case a\nX Y Z : ReflexiveGraph\nx✝¹ : HasProduct.prod X Y ⟶ Z\nf : Graph.V → Graph.V\nh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (f x) (f y)\nx : Graph.V\nx✝ y✝ : Graph.V\ne : Graph.E x✝ y✝\n⊢ Graph.E (x, x✝) (x, y✝)']</proofstate>
      exact ⟨ X.property x, e ⟩
     ⟩, by <proofstate>['X Y Z : ReflexiveGraph\nx✝ : HasProduct.prod X Y ⟶ Z\nf : Graph.V → Graph.V\nh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (f x) (f y)\n⊢ ∀ (x y : Graph.V),\n    Graph.E x y →\n      Graph.E ((fun x ↦ { down := { f := fun y ↦ f (x, y), pe := ⋯ } }) x)\n        ((fun x ↦ { down := { f := fun y ↦ f (x, y), pe := ⋯ } }) y)']</proofstate>
        intros _ _ ex _ _ ey <proofstate>['X Y Z : ReflexiveGraph\nx✝² : HasProduct.prod X Y ⟶ Z\nf : Graph.V → Graph.V\nh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (f x) (f y)\nx✝¹ y✝¹ : Graph.V\nex : Graph.E x✝¹ y✝¹\nx✝ y✝ : Graph.V\ney : Graph.E x✝ y✝\n⊢ Graph.E ((fun y ↦ f (x✝¹, y)) x✝) ((fun y ↦ f (y✝¹, y)) y✝)']</proofstate>
        apply h <proofstate>['case a\nX Y Z : ReflexiveGraph\nx✝² : HasProduct.prod X Y ⟶ Z\nf : Graph.V → Graph.V\nh : ∀ (x y : Graph.V), Graph.E x y → Graph.E (f x) (f y)\nx✝¹ y✝¹ : Graph.V\nex : Graph.E x✝¹ y✝¹\nx✝ y✝ : Graph.V\ney : Graph.E x✝ y✝\n⊢ Graph.E (x✝¹, x✝) (y✝¹, y✝)']</proofstate>
        exact ⟨ex, ey⟩
    ⟩

  curry_eval := by intros; rfl,

  curry_unique := by <proofstate>['⊢ ∀ {X Y Z : ReflexiveGraph} (g : X ⟶ Z.exp Y) (h : HasProduct.prod X Y ⟶ Z),\n    prod_map g (𝟙 Y) ≫ Z.eval Y = h →\n      (match h with\n        | { f := f, pe := h } => { f := fun x ↦ { down := { f := fun y ↦ f (x, y), pe := ⋯ } }, pe := ⋯ }) =\n        g']</proofstate>
    intro _ _ _ _ _ comm <proofstate>['X✝ Y✝ Z✝ : ReflexiveGraph\ng✝ : X✝ ⟶ Z✝.exp Y✝\nh✝ : HasProduct.prod X✝ Y✝ ⟶ Z✝\ncomm : prod_map g✝ (𝟙 Y✝) ≫ Z✝.eval Y✝ = h✝\n⊢ (match h✝ with\n    | { f := f, pe := h } => { f := fun x ↦ { down := { f := fun y ↦ f (x, y), pe := ⋯ } }, pe := ⋯ }) =\n    g✝']</proofstate>
    rw[←comm] <proofstate>['X✝ Y✝ Z✝ : ReflexiveGraph\ng✝ : X✝ ⟶ Z✝.exp Y✝\nh✝ : HasProduct.prod X✝ Y✝ ⟶ Z✝\ncomm : prod_map g✝ (𝟙 Y✝) ≫ Z✝.eval Y✝ = h✝\n⊢ (match prod_map g✝ (𝟙 Y✝) ≫ Z✝.eval Y✝ with\n    | { f := f, pe := h } => { f := fun x ↦ { down := { f := fun y ↦ f (x, y), pe := ⋯ } }, pe := ⋯ }) =\n    g✝']</proofstate>
    rfl

}
```
 Hooray! 
```lean
--hide
end ReflexiveGraph
--unhide
```

Uncurrying
===

```lean
def HasExp.uncurry.{u,v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C] [HasExp.{u, v} C]
  {X Y Z : C} (g : X ⟶ Z ^ Y) : X * Y ⟶ Z := (g * (𝟙 Y)) ≫ eval

open HasProduct HasExp in
theorem curry_uncurry.{u, v} {C : Type u}
   [Category.{v} C] [HP : HasProduct.{u, v} C] [HE : HasExp.{u, v} C]
   (X Y Z : C) (g : X * Y ⟶ Z)
  : uncurry (curry g) = g := by <proofstate>['C : Type u\ninst✝ : Category.{v, u} C\nHP : HasProduct C\nHE : HasExp C\nX Y Z : C\ng : X * Y ⟶ Z\n⊢ uncurry (curry g) = g']</proofstate>
    unfold uncurry <proofstate>['C : Type u\ninst✝ : Category.{v, u} C\nHP : HasProduct C\nHE : HasExp C\nX Y Z : C\ng : X * Y ⟶ Z\n⊢ (curry g * 𝟙 Y) ≫ HasExp.eval = g']</proofstate>
    apply curry_eval
```

An Example Theorem
===


 - prod_map (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) : (prod Y₁ Y₂) ⟶ (prod X₁ X₂)
 - curry (g : (prod X Y) ⟶ Z) : X ⟶ (exp Z Y)
 - uncurry (g : X ⟶ Z ^ Y) : X * Y ⟶ Z

```lean
open HasProduct in
@[simp]
def prod_swap.{u, v} {C : Type u} (X Y : C) [Category.{v} C] [HasProduct.{u, v} C]
   : X * Y ⟶ Y * X := pair π₂ π₁


open HasProduct HasExp in
theorem exp_prod.{u, v} (C : Type u) [Category.{v} C] [HasProduct.{u, v} C] [HasExp.{u, v} C]
    (X Y Z : C) : ∃ f : Iso ((X^Y)^Z) (X^(Y*Z)), True := by <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\n⊢ ∃ f, True']</proofstate>
 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\n⊢ ∃ f, True']</proofstate>
    let f1 : (X^Y)^Z ⟶ X^(Y*Z) := <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\n⊢ ∃ f, True']</proofstate>
        curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ eval) (π₂ ≫ π₁) ≫ eval) <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\n⊢ ∃ f, True']</proofstate>
 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\n⊢ ∃ f, True']</proofstate>
    let f2 : X^(Y*Z) ⟶ (X^Y)^Z := <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ ∃ f, True']</proofstate>
        curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ eval)) <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ ∃ f, True']</proofstate>
 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ ∃ f, True']</proofstate>
    use ⟨
      f1,
      f2,
      by <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ f1 ≫ f2 = 𝟙 ((X ^ Y) ^ Z)']</proofstate>
        unfold f1 f2 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval) ≫\n      curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval)) =\n    𝟙 ((X ^ Y) ^ Z)']</proofstate>
        simp[prod_map,Category.comp_id] <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ curry (pair (pair π₁ (π₂ ≫ π₂) ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval) ≫\n      curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval)) =\n    𝟙 ((X ^ Y) ^ Z)']</proofstate>
 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ curry (pair (pair π₁ (π₂ ≫ π₂) ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval) ≫\n      curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval)) =\n    𝟙 ((X ^ Y) ^ Z)']</proofstate>
        sorry,
      by <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ f2 ≫ f1 = 𝟙 (X ^ (Y * Z))']</proofstate>
        unfold f1 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ f2 ≫ curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval) = 𝟙 (X ^ (Y * Z))']</proofstate>
        unfold f2 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval)) ≫\n      curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval) =\n    𝟙 (X ^ (Y * Z))']</proofstate>
 <proofstate>['C : Type u\ninst✝² : Category.{v, u} C\ninst✝¹ : HasProduct C\ninst✝ : HasExp C\nX Y Z : C\nf1 : (X ^ Y) ^ Z ⟶ X ^ (Y * Z) := curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval)\nf2 : X ^ (Y * Z) ⟶ (X ^ Y) ^ Z := curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval))\n⊢ curry (curry (pair (π₁ ≫ π₁) (pair π₂ (π₁ ≫ π₂)) ≫ HasExp.eval)) ≫\n      curry (pair (prod_map (𝟙 ((X ^ Y) ^ Z)) π₂ ≫ HasExp.eval) (π₂ ≫ π₁) ≫ HasExp.eval) =\n    𝟙 (X ^ (Y * Z))']</proofstate>
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
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

