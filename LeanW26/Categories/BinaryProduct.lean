import Mathlib
import LeanW26.Categories.Category

namespace LeanW26

open CategoryTheory

/-
Category Theory: Binary Products
===

A `binary product` of two objects `X₁` and `X₂` in a category is an object called `X₁ × X₂`.

A `projection` of a binary product throws away one of the parts:

```lean
   π₁ (X₁ × X₂) = X₁
   π₂ (X₁ × X₂) = X₂
```

<img src="https://docs.google.com/drawings/d/e/2PACX-1vRcGx-5-JPZkvvFdkf8-u-L67BcyFh-GzLcfgk4NBjPaLivE2nSPQIdrbg5y4AQMIysqqMWeXd3kg1y/pub?w=576&amp;h=315" height=40%>

Universal Property for Binary Products
===

> For every object `Y` and morphisms `f₁ : Y ⟶ X₁`
> and `f₂ : Y ⟶ X₂` there is a unique morphism `f : Y ⟶ X₁ × X₂` such that
> `f ≫ π₁ = f₁` and `f ≫ π₂ = f₂`.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQPk2cl9FCCrOcGcwbIJtqL_-lP-d20u6wWSJEZhAsc6EwopVkNBU2sjAmJJZwkj7nXZb8RU4cQoc4H/pub?w=960&amp;h=720" height=50%>


The `pair` function
===

We call the unique morphism in the universal property for binary products `pair`. In Lean
it has type

```lean
pair {X₁ X₂ Y : C} (_ : Y ⟶ X₁) (_ : Y ⟶ X₂) : Y ⟶ (prod X₁ X₂)
```

Binary Products in Lean
===

The properties `pairᵢ` record the universal property, and the `unique_pair`
property records the requirement the morphism is unique. -/

@[ext]
class HasProduct.{u,v} (C : Type u) [Category.{v} C] where

  prod : C → C → C
  π₁ {X₁ X₂ : C} : (prod X₁ X₂) ⟶ X₁
  π₂ {X₁ X₂ : C} : (prod X₁ X₂) ⟶ X₂
  pair {X₁ X₂ Y : C} (_ : Y ⟶ X₁) (_ : Y ⟶ X₂) : Y ⟶ (prod X₁ X₂)

  pair₁ {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) : pair f₁ f₂ ≫ π₁ = f₁
  pair₂ {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) : pair f₁ f₂ ≫ π₂ = f₂
  pair_unique {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (h : Y ⟶ prod X₁ X₂)
    (h_comm₁ : h ≫ π₁ = f₁) (h_comm₂ : h ≫ π₂ = f₂) : h = pair f₁ f₂

--hide
namespace HasProduct
--unhide

/-
Product Notation
===

Instead of writing `prod A B` we would rather write `A * B`. So we instantiate the notation
classes for `*`:
-/


instance inst_hmul {C : Type*} [Category C] [HasProduct C] : HMul C C C where
  hMul := prod

instance inst_mul {C : Type*} [Category C] [HasProduct C] : Mul C where
  mul := prod

/- For example -/

example {C : Type*} [Category C] [HasProduct C] (A B : C) : A*B = A*B := by rfl

/-

Annoyingly, there does not seem to be a notation class for × in Mathlib, perhaps
because the powers that be want to use that symbol exlusively for cartesian products
of types.

Products are Associative
===
-/

@[simp, reassoc]
lemma pair_comp_π₁.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
  {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} :
  pair f g ≫ π₁ = f := pair₁ f g

@[simp, reassoc]
lemma pair_comp_π₂.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
  {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} :
  pair f g ≫ π₂ = g := pair₂ f g

-- Uniqueness of pair morphism (implication form)
-- lemma pair_eq_of_commutes.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
--   {X Y Z : C} {h : Z ⟶ X * Y} {f : Z ⟶ X} {g : Z ⟶ Y}
--   {h₁ : h ≫ π₁ = f} {h₂ : h ≫ π₂ = g} :
--   h = pair f g := pair_unique f g h h₁ h₂

-- Pair congruence
--@[simp, reassoc]
-- lemma pair_congr.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
--   {X Y Z : C} {f₁ f₁' : Z ⟶ X} {f₂ f₂' : Z ⟶ Y}
--   {h₁ : f₁ = f₁'} {h₂ : f₂ = f₂'} :
--   pair f₁ f₂ = pair f₁' f₂' := by rw [h₁, h₂]

@[simp, reassoc]
theorem pair_id.{u,v} {C : Type u} [Category.{v} C] [HasProduct C] {X Y : C} :
    pair (π₁ : X*Y ⟶ X) (π₂ : X*Y ⟶ Y) = 𝟙 (X*Y) := by
    apply Eq.symm
    apply pair_unique _ _ (𝟙 (X*Y))
    · apply Category.id_comp
    · apply Category.id_comp

@[simp]
lemma prod_id_unique.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
  {X Y : C} (f : X * Y ⟶ X * Y) (h₁ : f ≫ π₁ = π₁) (h₂ : f ≫ π₂ = π₂)
  : f = 𝟙 (X*Y) := by
    rw[pair_unique π₁ π₂ f h₁ h₂]
    apply pair_id

@[simp, reassoc]
lemma comp_pair.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
  {W X Y Z : C} {h : W ⟶ X} {f : X ⟶ Y} {g : X ⟶ Z} :
  h ≫ pair f g = pair (h ≫ f) (h ≫ g) := by
  apply pair_unique
  · simp [Category.assoc]
  · simp [Category.assoc]

lemma pair_eta.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C]
 {W X Y : C} {h : W ⟶ X * Y} :
  pair (h ≫ (π₁ : X*Y ⟶ X)) (h ≫ (π₂ : X*Y ⟶ Y)) = h := by
  exact (pair_unique _ _ _ (by simp) (by simp)).symm

@[simp]
def prod_assoc.{u, v} {C : Type u} [Category.{v} C] [HasProduct.{u, v} C] {X Y Z : C}
  : (X*Y)*Z ≅ X*(Y*Z) :=

    let f₁ := π₁ ≫ π₁
    let f₂ := pair (π₁ ≫ π₂) π₂
    let f := pair f₁ f₂
    let g₁ := pair π₁ (π₂ ≫ π₁)
    let g₂ := π₂ ≫ π₂
    let g := pair g₁ g₂

    {
      hom := f,
      inv := g,
      hom_inv_id := by
        apply prod_id_unique
        · simp?[f,g,f₁,f₂,g₁,g₂,←Category.assoc]
          apply pair_eta
        · simp[f,g,f₁,f₂,g₁,g₂,←Category.assoc],
      inv_hom_id := by
         apply prod_id_unique
         · simp[f,g,f₁,f₂,g₁,g₂,←Category.assoc]
         · simp[f,g,f₁,f₂,g₁,g₂,←Category.assoc]
           apply pair_eta
    }

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

When `f` and `g` are morphisms, we want to write `f*g` for their prodict, so
we instantiate the notation class for `*` for morphisms as well.

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

--hide
namespace TensorProd
--unhide

/-
Example: Tensor Product Properties
===

To form an instance of a `HasProduct` It will be convenient to have the following
properties defined as theorems, which state that products preserve edges.

-/

theorem left {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → G.E x.1 y.1 := by
  intro x y h
  exact h.left

theorem right {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → H.E x.2 y.2 := by
  intro x y h
  exact h.right

--hide
end TensorProd
--unhide

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




--hide
end HasProduct
end LeanW26
--unhide
