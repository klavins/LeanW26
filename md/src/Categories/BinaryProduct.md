
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
the morphism is unique. 
```lean
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
```

Product Notation
===

```lean
instance inst_hmul {C : Type*} [Category C] [HasProduct C] : HMul C C C where
  hMul := prod

instance inst_mul {C : Type*} [Category C] [HasProduct C] : Mul C where
  mul := prod

example {C : Type*} [Category C] [HasProduct C] (A B : C) : A*B = A*B := by rfl
```


Annoyingly, there does not seem to be a notation class for × in Mathlib, perhaps
because the powers that be want to use that symbol exlusively for cartesian products
of types.


Pairs of Morphisms
===

Pair only describes how to take the product of morphisms with the same domain.
The following method, which builds on `pair`, allows products of arbitary morphisms,
which will be useful in defining exponentials later.  
```lean
def prod_map.{u} {C : Type u} [Category C] [HasProduct C]
             {X₁ Y₁ X₂ Y₂ : C} (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
  : (prod Y₁ Y₂) ⟶ (prod X₁ X₂) :=
  let P := prod Y₁ Y₂
  let g₁ : P ⟶ X₁ := π₁ ≫ f₁
  let g₂ : P ⟶ X₂ := π₂ ≫ f₂
  pair g₁ g₂
```

Notation for Pairs of Morphisms
===


```lean
instance inst_hmul_morph {C : Type*} [Category C] [HasProduct C] {Y₁ X₁ Y₂ X₂ : C} :
         HMul (Y₁ ⟶ X₁) (Y₂ ⟶ X₂) ((prod Y₁ Y₂) ⟶ (prod X₁ X₂)) where
  hMul := prod_map

namespace Temp

variable (C : Type*) [Category C] [HasProduct C] (X Y : C) (f g : X ⟶ Y)
#check f * g
#check π₁ ≫ f * g ≫ 𝟙 Y

end Temp
```

Example: Graphs Have Products
===

Graphs have products called Tensor Products, which we can use to instantiate the `HasProduct` class.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vS8m1ASMsZn0P7p6k0rOGj-8KKBhahoNL7SvrASBquIOwZdxX3_t_49JfFJ7WtowCD-AvSfSe1vkldt/pub?w=814&amp;h=368" height=30% \>


```lean
def TensorProd (G H : Graph) : Graph := {
  V := G.V × H.V,
  E := fun (u1,v1) (u2,v2) => G.E u1 u2 ∧ H.E v1 v2
}

namespace TensorProd
```

Example: Tensor Product Properties
===

To form an insstance of a `HasProduct` It will be convenient to have the following
properties defined as theorems.


```lean
theorem left {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → G.E x.1 y.1 := by
  intro x y h
  exact h.left

theorem right {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → H.E x.2 y.2 := by
  intro x y h
  exact h.right

end TensorProd
```

Example: Graphs Have Products
===

Now we can instantiate the `HasProduct` class for graphs.


```lean
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

end LeanW26
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

