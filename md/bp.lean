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

<img src="https://docs.google.com/drawings/d/e/2PACX-1vRcGx-5-JPZkvvFdkf8-u-L67BcyFh-GzLcfgk4NBjPaLivE2nSPQIdrbg5y4AQMIysqqMWeXd3kg1y/pub?w=576&amp;h=315" width=40%>

Universal Property for Binary Products
===

> For every object `Y` and morphisms `f₁ : Y ⟶ X₁`
> and `f₂ : Y ⟶ X₂` there is a unique morphism `f : Y ⟶ X₁ × X₂` such that
> `f ≫ π₁ = f₁` and `f ≫ π₂ = f₂`.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQPk2cl9FCCrOcGcwbIJtqL_-lP-d20u6wWSJEZhAsc6EwopVkNBU2sjAmJJZwkj7nXZb8RU4cQoc4H/pub?w=960&amp;h=720" width=60%>


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

attribute [simp, reassoc] HasProduct.pair₁ HasProduct.pair₂

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

Theorems
===

Next we'll prove some theorems about Products, eventually getting to
the nice result that products are associative `(X*Y)*Z = X*(Y*Z)`.

We'll use the following variables repeatedly, so it is worth specifing them
globally in the rest of the file for this code.

-/

universe u v
variable {C : Type u} [Category.{v} C] [HasProduct C] {W X Y Z : C}

/-
Pairs of Projections
===

The first theorem states that when you take a pair of projections, you
get the identity map.

<!-- https://q.uiver.app/#q=WzAsMyxbMSwwLCJYKlkiXSxbMiwwLCJZIl0sWzAsMCwiWCJdLFswLDIsIlxccGlfMSIsMl0sWzAsMSwiXFxwaV8yIl0sWzAsMCwiMV97WCpZfSJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMyxbMSwwLCJYKlkiXSxbMiwwLCJZIl0sWzAsMCwiWCJdLFswLDIsIlxccGlfMSIsMl0sWzAsMSwiXFxwaV8yIl0sWzAsMCwiMV97WCpZfSJdXQ==&embed" width="351" height="220" style="border-radius: 8px; border: none;"></iframe>


-/

@[simp, reassoc]
theorem pair_id : pair (π₁ : X*Y ⟶ X) (π₂ : X*Y ⟶ Y) = 𝟙 (X*Y) := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nX Y : C\n⊢ pair π₁ π₂ = 𝟙 (X * Y)']</proofstate>
    apply Eq.symm <proofstate>['case h\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nX Y : C\n⊢ 𝟙 (X * Y) = pair π₁ π₂']</proofstate>
    apply pair_unique _ _ (𝟙 (X*Y)) <proofstate>['case h.h_comm₁\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nX Y : C\n⊢ 𝟙 (X * Y) ≫ π₁ = π₁', 'case h.h_comm₂\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nX Y : C\n⊢ 𝟙 (X * Y) ≫ π₂ = π₂']</proofstate>
    · apply Category.id_comp
    · apply Category.id_comp


/-
Conditions for a map to be the Identity
===

The next theorem describes when `f : X * Y ⟶ X * Y` is the identity on
`X * Y`.
-/

@[simp]
lemma prod_id_unique (f : X * Y ⟶ X * Y) (h₁ : f ≫ π₁ = π₁) (h₂ : f ≫ π₂ = π₂)
  : f = 𝟙 (X*Y) := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nX Y : C\nf : X * Y ⟶ X * Y\nh₁ : f ≫ π₁ = π₁\nh₂ : f ≫ π₂ = π₂\n⊢ f = 𝟙 (X * Y)']</proofstate>
    rw[pair_unique π₁ π₂ f h₁ h₂] <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nX Y : C\nf : X * Y ⟶ X * Y\nh₁ : f ≫ π₁ = π₁\nh₂ : f ≫ π₂ = π₂\n⊢ pair π₁ π₂ = 𝟙 (X * Y)']</proofstate>
    apply pair_id

/-
Composing Pairs
===

This theorem shows how to compose pairs.
-/

@[simp, reassoc]
lemma comp_pair {h : W ⟶ X} {f : X ⟶ Y} {g : X ⟶ Z} :
  h ≫ pair f g = pair (h ≫ f) (h ≫ g) := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\nh : W ⟶ X\nf : X ⟶ Y\ng : X ⟶ Z\n⊢ h ≫ pair f g = pair (h ≫ f) (h ≫ g)']</proofstate>
  apply pair_unique <proofstate>['case h_comm₁\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\nh : W ⟶ X\nf : X ⟶ Y\ng : X ⟶ Z\n⊢ (h ≫ pair f g) ≫ π₁ = h ≫ f', 'case h_comm₂\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\nh : W ⟶ X\nf : X ⟶ Y\ng : X ⟶ Z\n⊢ (h ≫ pair f g) ≫ π₂ = h ≫ g']</proofstate>
  · simp [Category.assoc]
  · simp [Category.assoc]

/-
Composing with Projections
===

This statement covers conposition of a morphism with the projections.
-/

lemma pair_eta {h : W ⟶ X * Y} :
  pair (h ≫ (π₁ : X*Y ⟶ X)) (h ≫ (π₂ : X*Y ⟶ Y)) = h := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y : C\nh : W ⟶ X * Y\n⊢ pair (h ≫ π₁) (h ≫ π₂) = h']</proofstate>
  exact (pair_unique _ _ _ (by simp) (by simp)).symm

/-

<!-- https://q.uiver.app/#q=WzAsNCxbMCwxLCJXIl0sWzIsMSwiWCpZIl0sWzMsMCwiWCJdLFszLDIsIlkiXSxbMCwxLCJoIiwwLHsiY3VydmUiOi0zfV0sWzEsMywiXFxwaV8yIiwyXSxbMSwyLCJcXHBpXzEiXSxbMCwxLCJwYWlyIFxcOyAoaCBcXGdnIFxccGlfMSkgKGggXFxnZyBcXHBpXzIpIiwyLHsib2Zmc2V0IjotMywiY3VydmUiOjMsInNob3J0ZW4iOnsidGFyZ2V0IjoxMH19XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMCwxLCJXIl0sWzIsMSwiWCpZIl0sWzMsMCwiWCJdLFszLDIsIlkiXSxbMCwxLCJoIiwwLHsiY3VydmUiOi0zfV0sWzEsMywiXFxwaV8yIiwyXSxbMSwyLCJcXHBpXzEiXSxbMCwxLCJwYWlyIFxcOyAoaCBcXGdnIFxccGlfMSkgKGggXFxnZyBcXHBpXzIpIiwyLHsib2Zmc2V0IjotMywiY3VydmUiOjMsInNob3J0ZW4iOnsidGFyZ2V0IjoxMH19XV0=&embed" width="320" height="280" style="border-radius: 8px; border: none;"></iframe>

-/

/-
Associativity Diagram
===

<table><tr>

<td>
<!-- https://q.uiver.app/#q=WzAsNyxbMSwwLCIoWCpZKSpaIl0sWzAsMSwiWCpZIl0sWzIsMSwiWiJdLFsxLDIsIlkiXSxbMCwzLCJYIl0sWzIsMywiWSpaIl0sWzEsNCwiWCooWSpaKSJdLFswLDEsIlxccGlfMSIsMl0sWzAsMiwiXFxwaV8yIl0sWzEsNCwiXFxwaV8xIiwyXSxbMSwzLCJcXHBpXzIiXSxbNSwzLCJcXHBpXzEiXSxbNiw1LCJcXHBpXzIiXSxbNiw0LCJcXHBpXzEiXSxbNSwyLCJcXHBpXzIiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNyxbMSwwLCIoWCpZKSpaIl0sWzAsMSwiWCpZIl0sWzIsMSwiWiJdLFsxLDIsIlkiXSxbMCwzLCJYIl0sWzIsMywiWSpaIl0sWzEsNCwiWCooWSpaKSJdLFswLDEsIlxccGlfMSIsMl0sWzAsMiwiXFxwaV8yIl0sWzEsNCwiXFxwaV8xIiwyXSxbMSwzLCJcXHBpXzIiXSxbNSwzLCJcXHBpXzEiXSxbNiw1LCJcXHBpXzIiXSxbNiw0LCJcXHBpXzEiXSxbNSwyLCJcXHBpXzIiLDJdXQ==&embed" width="300" height="350" style="border-radius: 8px; border: none;"></iframe>
</td>

<td>
π₁ ≫ π₂ : (X×Y)×Z ⟶ Y<br>
π₂ : (X×Y)×Z ⟶ Z<br>
π₁ ≫ π₁ : (X×Y)×Z ⟶ X<br>
⟹<br>
pair (π₁ ≫ π₂) π₂ : (X×Y)×Z ⟶ Y×Z<br>
pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂) : (X×Y)×Z  ⟶ X×(Y×Z)<br>
<br>
Similarly,<br>
pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂) : X×(Y×Z) ⟶ (X×Y)×Z<br>
</td>
</tr></table>

Proof of Associativity
===

-/

@[simp]
def prod_assoc : (X*Y)*Z ≅ X*(Y*Z) :=
    {
      hom := pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂),
      inv := pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂),
      hom_inv_id := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂) ≫ pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂) = 𝟙 (X * Y * Z)']</proofstate>
        apply prod_id_unique <proofstate>['case h₁\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ (pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂) ≫ pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂)) ≫ π₁ = π₁', 'case h₂\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ (pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂) ≫ pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂)) ≫ π₂ = π₂']</proofstate>
        · simp[←Category.assoc] <proofstate>['case h₁\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ pair (π₁ ≫ π₁) (π₁ ≫ π₂) = π₁']</proofstate>
          apply pair_eta
        · simp[←Category.assoc],
      inv_hom_id := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂) ≫ pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂) = 𝟙 (X * (Y * Z))']</proofstate>
         apply prod_id_unique <proofstate>['case h₁\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ (pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂) ≫ pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂)) ≫ π₁ = π₁', 'case h₂\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ (pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂) ≫ pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂)) ≫ π₂ = π₂']</proofstate>
         · simp[←Category.assoc]
         · simp[←Category.assoc] <proofstate>['case h₂\nC : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ pair (π₂ ≫ π₁) (π₂ ≫ π₂) = π₂']</proofstate>
           apply pair_eta
    }

/-
Pairs of Morphisms
===

Pair only describes how to take the product of morphisms with the same domain.
The following method, which builds on `pair`, allows products of arbitary morphisms,
which will be useful in defining exponentials later.  -/

def prod_map {X₁ Y₁ X₂ Y₂ : C} (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
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

<img src="https://docs.google.com/drawings/d/e/2PACX-1vS8m1ASMsZn0P7p6k0rOGj-8KKBhahoNL7SvrASBquIOwZdxX3_t_49JfFJ7WtowCD-AvSfSe1vkldt/pub?w=814&amp;h=368" width=50% \>

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
  ∀ x y, (TensorProd G H).E x y → G.E x.1 y.1 := by <proofstate>['G : Graph\nH : Graph\n⊢ ∀ (x y : Graph.V), Graph.E x y → Graph.E x.1 y.1']</proofstate>
  intro x y h <proofstate>['G : Graph\nH : Graph\nx y : Graph.V\nh : Graph.E x y\n⊢ Graph.E x.1 y.1']</proofstate>
  trace_state <proofstate>['G : Graph\nH : Graph\nx y : Graph.V\nh : Graph.E x y\n⊢ Graph.E x.1 y.1']</proofstate>
  exact h.left

theorem right {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → H.E x.2 y.2 := by <proofstate>['G : Graph\nH : Graph\n⊢ ∀ (x y : Graph.V), Graph.E x y → Graph.E x.2 y.2']</proofstate>
  intro x y h <proofstate>['G : Graph\nH : Graph\nx y : Graph.V\nh : Graph.E x y\n⊢ Graph.E x.2 y.2']</proofstate>
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
  pair := fun {X Y Z} f₁ f₂ => ⟨ fun z => ( f₁.f z, f₂.f z ), by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X✝ Y✝ Z✝ : C\nX Y Z : Graph\nf₁ : Z ⟶ X\nf₂ : Z ⟶ Y\n⊢ ∀ (x y : Graph.V), Graph.E x y → Graph.E ((fun z ↦ (f₁.f z, f₂.f z)) x) ((fun z ↦ (f₁.f z, f₂.f z)) y)']</proofstate>
      intro x y h <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X✝ Y✝ Z✝ : C\nX Y Z : Graph\nf₁ : Z ⟶ X\nf₂ : Z ⟶ Y\nx y : Graph.V\nh : Graph.E x y\n⊢ Graph.E ((fun z ↦ (f₁.f z, f₂.f z)) x) ((fun z ↦ (f₁.f z, f₂.f z)) y)']</proofstate>
      exact ⟨ f₁.pe x y h, f₂.pe x y h ⟩
    ⟩
  pair₁ := by intros; rfl
  pair₂ := by intros; rfl
  pair_unique := by <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\n⊢ ∀ {X₁ X₂ Y : Graph} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (h : Y ⟶ TensorProd X₁ X₂),\n    h ≫ { f := Prod.fst, pe := ⋯ } = f₁ →\n      h ≫ { f := Prod.snd, pe := ⋯ } = f₂ → h = { f := fun z ↦ (f₁.f z, f₂.f z), pe := ⋯ }']</proofstate>
    intro _ _ _ _ _ _ h1 h2 <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\nX₁✝ X₂✝ Y✝ : Graph\nf₁✝ : Y✝ ⟶ X₁✝\nf₂✝ : Y✝ ⟶ X₂✝\nh✝ : Y✝ ⟶ TensorProd X₁✝ X₂✝\nh1 : h✝ ≫ { f := Prod.fst, pe := ⋯ } = f₁✝\nh2 : h✝ ≫ { f := Prod.snd, pe := ⋯ } = f₂✝\n⊢ h✝ = { f := fun z ↦ (f₁✝.f z, f₂✝.f z), pe := ⋯ }']</proofstate>
    rw[←h1,←h2] <proofstate>['C : Type u\ninst✝¹ : Category.{v, u} C\ninst✝ : HasProduct C\nW X Y Z : C\nX₁✝ X₂✝ Y✝ : Graph\nf₁✝ : Y✝ ⟶ X₁✝\nf₂✝ : Y✝ ⟶ X₂✝\nh✝ : Y✝ ⟶ TensorProd X₁✝ X₂✝\nh1 : h✝ ≫ { f := Prod.fst, pe := ⋯ } = f₁✝\nh2 : h✝ ≫ { f := Prod.snd, pe := ⋯ } = f₂✝\n⊢ h✝ = { f := fun z ↦ ((h✝ ≫ { f := Prod.fst, pe := ⋯ }).f z, (h✝ ≫ { f := Prod.snd, pe := ⋯ }).f z), pe := ⋯ }']</proofstate>
    rfl
}




--hide
end HasProduct
end LeanW26
--unhide

