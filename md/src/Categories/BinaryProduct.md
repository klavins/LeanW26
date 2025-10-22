
Category Theory: Binary Products
===

A ***binary product*** of two objects `X₁` and `X₂` in a category is an object called `X₁ × X₂`.

A ***projection*** of a binary product throws away one of the parts:

```lean
   π₁ (X₁ × X₂) = X₁
   π₂ (X₁ × X₂) = X₂
```

<img src="https://docs.google.com/drawings/d/e/2PACX-1vRcGx-5-JPZkvvFdkf8-u-L67BcyFh-GzLcfgk4NBjPaLivE2nSPQIdrbg5y4AQMIysqqMWeXd3kg1y/pub?w=576&amp;h=315"
     width=30%>

Universal Property for Binary Products
===

For every object `Y` and morphisms `f₁ : Y ⟶ X₁`
and `f₂ : Y ⟶ X₂` there is a unique morphism `f : Y ⟶ X₁ × X₂` such that
`f ≫ π₁ = f₁` and `f ≫ π₂ = f₂`.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vQPk2cl9FCCrOcGcwbIJtqL_-lP-d20u6wWSJEZhAsc6EwopVkNBU2sjAmJJZwkj7nXZb8RU4cQoc4H/pub?w=960&amp;h=720"
     width=40%>

We call the unique morphism in the universal property for binary products `pair`. In Lean
it has type

```lean
pair {X₁ X₂ Y : C} (_ : Y ⟶ X₁) (_ : Y ⟶ X₂) : Y ⟶ (prod X₁ X₂)
```

Binary Products in Lean
===

The properties `pairᵢ` record the universal property, and the `unique_pair`
property records the requirement the morphism is unique. 
```lean
@[ext]
class HasProduct.{u,v} (C : Type u) [Category.{v} C] where

  prod : C → C → C
  π₁ {X₁ X₂ : C} : (prod X₁ X₂) ⟶ X₁
  π₂ {X₁ X₂ : C} : (prod X₁ X₂) ⟶ X₂
  pair {X₁ X₂ Y : C} (_ : Y ⟶ X₁) (_ : Y ⟶ X₂) : Y ⟶ (prod X₁ X₂)

  pair₁ {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    : pair f₁ f₂ ≫ π₁ = f₁ := by aesop_cat
  pair₂ {X₁ X₂ Y : C} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    : pair f₁ f₂ ≫ π₂ = f₂ := by aesop_cat
  pair_unique {X₁ X₂ Y : C} {h : Y ⟶ prod X₁ X₂}
    : h = pair (h ≫ π₁) (h ≫ π₂) := by aesop_cat

--hide
attribute [simp, reassoc] HasProduct.pair₁ HasProduct.pair₂
namespace HasProduct

universe u v
variable {C : Type u} [Category.{v} C] [HasProduct C] {A B U V W W' X X₁ X₂ Y Y₁ Y₂ Z : C}

--unhide
```

Product Notation
===

Instead of writing `prod A B` we would rather write `A * B`. So we instantiate the notation
classes for `*`:

```lean
instance inst_hmul {C : Type*} [Category C] [HasProduct C] : HMul C C C where
  hMul := prod

instance inst_mul {C : Type*} [Category C] [HasProduct C] : Mul C where
  mul := prod
```
 For example 
```lean
example {C : Type*} [Category C] [HasProduct C] (A B : C) : A*B = A*B := by rfl
```

Pairs of Morphisms
===

Pair only describes how to take the product of morphisms with the same domain.
The following method, which builds on `pair`, allows products of arbitary morphisms,
which will be useful in defining exponentials later.  
```lean
def prod_map {X₁ Y₁ X₂ Y₂ : C} (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
  : Y₁ * Y₂ ⟶ X₁ * X₂ := pair (π₁ ≫ f₁) (π₂ ≫ f₂)
```

Notation for Pairs of Morphisms
===

When `f` and `g` are morphisms, we want to write `f*g` for their prodict, so
we instantiate the notation class for `*` for morphisms as well.
```lean
notation "‹" f₁ ", " f₂ "›" => prod_map f₁ f₂

namespace Temp

variable (C : Type*) [Category C] [HasProduct C] (X Y : C) (f g : X ⟶ Y)
#check ‹f,g›
#check ‹ π₁ ≫ f, g ≫ 𝟙 Y ›

end Temp
```

Helper Theorems
===

```lean
@[simp, reassoc]
theorem pair_id : pair (π₁ : X*Y ⟶ X) (π₂ : X*Y ⟶ Y) = 𝟙 (X*Y) := by
    apply Eq.symm
    rw[←Category.id_comp π₁, ←Category.id_comp π₂]
    apply pair_unique

@[simp, reassoc]
lemma comp_pair {h : W ⟶ X} {f : X ⟶ Y} {g : X ⟶ Z} :
  h ≫ pair f g = pair (h ≫ f) (h ≫ g) := by
  rw[pair_unique (h := h ≫ pair f g )]
  simp

@[simp]
theorem prod_to_pair {f₁ : Y₁ ⟶ X₁} {f₂ : Y₂ ⟶ X₂}
   : ‹f₁,f₂› = pair (π₁ ≫ f₁) (π₂ ≫ f₂) := by rfl

@[simp]
theorem prod_map_comp {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : U ⟶ V} {g₂ : V ⟶ W}
  : ‹ f₁ ≫ f₂, g₁ ≫ g₂ › = ‹ f₁, g₁ › ≫ ‹f₂, g₂› := by
  simp[←Category.assoc] -- uses comp_pair and prod_to_pair

theorem pair_unique_simp {h : Y ⟶ prod X₁ X₂} : pair (h ≫ π₁) (h ≫ π₂) = h := by
  apply Eq.symm
  exact pair_unique

theorem pair_unique_simp2 {f : W ⟶ X * Y * Z}
  : pair (f ≫ π₁ ≫ π₁) (f ≫ π₁ ≫ π₂) = f ≫ π₁ := by
  simp[←Category.assoc]
  apply pair_unique_simp

theorem pair_unique_simp3 {f : W ⟶ X * (Y * Z)}
  : pair (f ≫ π₂ ≫ π₁) (f ≫ π₂ ≫ π₂) = f ≫ π₂ := by
  simp[←Category.assoc]
  apply pair_unique_simp

@[simp]
theorem hom_ext {A B : C} {f g : X ⟶ A * B} {h₁ : f ≫ π₁ = g ≫ π₁} {h₂ : f ≫ π₂ = g ≫ π₂}
  : f = g := by
    rw[pair_unique (h := f)]
    rw[pair_unique (h := g)]
    rw[h₁,h₂]

@[simp]
lemma prod_map_fst {f : A ⟶ X} {g : B ⟶ Y} :
    ‹f,g› ≫ π₁ = π₁ ≫ f := by simp

@[simp]
lemma prod_map_snd {f : A ⟶ X} {g : B ⟶ Y} :
    ‹f,g› ≫ π₂ = π₂ ≫ g := by simp
```

Projection Functors
===

```lean
def Fst : (C × C) ⥤ C where
  obj XY := XY.1
  map h := h.1

def Snd : (C × C) ⥤ C where
  obj XY := XY.2
  map h := h.2
```

The Product Bifunctor
===

```lean
def ProdBifunctor : (C × C) ⥤ C where
  obj XY := XY.1 * XY.2
  map { XY XY' } (h : XY ⟶ XY') := prod_map (C := C) h.1 h.2
  map_id := by
    intro XY
    simp[prod_map] -- uses pair_id
  map_comp := by
    intro X Y Z f g
    simp only [prod_comp, prod_map_comp]
```

Naturality
===

```lean
def π₁_nat : ProdBifunctor ⟶ Fst (C:=C) where
  app XY := π₁
  naturality {XY XY'} (h : XY ⟶ XY') := by
    simp[ProdBifunctor,Fst]

def π₂_nat : ProdBifunctor ⟶ Snd (C:=C) where
  app XY := π₂
  naturality {XY XY'} (h : XY ⟶ XY') := by
    simp[ProdBifunctor,Snd]
```

Proving Associativity
===
Yoneda says to show `X ≅ Y` we need to show `Z ⟶ X ≅ Z ⟶ Y`.

So to show `(A*B)*C ≅ A*(B*C)` it suffices to show
`Z ⟶ (A*B)*C ≅ Z ⟶ A*(B*C)`.

We'll do this by showing
- `Z ⟶ (A*B)*C ≅ (Z ⟶ A ⨯ Z ⟶ B) × (Z ⟶ C)`
- `Z ⟶ A*(B*C) ≅ (Z ⟶ A) ⨯ (Z ⟶ B × Z ⟶ C)`

Then via associativity of × in the category Set,
`(Z ⟶ A ⨯ Z ⟶ B) × (Z ⟶ C) ≅ (Z ⟶ A) ⨯ (Z ⟶ B × Z ⟶ C)`

Transitivity allows us to conclude `Z ⟶ (A*B)*C ≅ Z ⟶ A*(B*C)`
after which we can applyt the Yoneda Lemma.



Step One
===

```lean
def t1 : (W ⟶ (X*Y)*Z) ≃ ((W ⟶ X) × (W ⟶ Y)) × (W ⟶ Z) := {
      toFun f := ( ( f ≫ π₁ ≫ π₁ , f ≫ π₁ ≫ π₂ ), f ≫ π₂ ),
      invFun := fun ⟨ ⟨ f1, f2 ⟩, f3 ⟩  => pair (pair f1 f2) f3,
      left_inv := by
        intro f
        simp[pair_unique_simp2,pair_unique_simp],
      right_inv := by
        intro f
        simp[←Category.assoc]
  }
```

Step Two
===

```lean
def t2 : (W ⟶ X*(Y*Z)) ≃ (W ⟶ X) × ((W ⟶ Y) × (W ⟶ Z)) := {
      toFun f := ( f ≫ π₁, ( f ≫ π₂ ≫ π₁ , f ≫ π₂ ≫ π₂ ) ),
      invFun := fun ⟨ f1, ⟨ f2, f3 ⟩ ⟩  => pair f1 (pair f2 f3),
      left_inv := by
        intro f
        simp[pair_unique_simp3,pair_unique_simp],
      right_inv := by
        intro f
        simp[←Category.assoc]
  }
```

Step Three
===

```lean
def t3 : ((W ⟶ X) × (W ⟶ Y)) × (W ⟶ Z) ≃ (W ⟶ X) × ((W ⟶ Y) × (W ⟶ Z)) := {
  toFun f := (f.1.1,(f.1.2,f.2)),
  invFun f := ((f.1,f.2.1),f.2.2),
  left_inv := by exact congrFun rfl,
  right_inv := by exact congrFun rfl
}
```

Naturality
===

```lean
def homAssocEquiv : (W ⟶ (X * Y) * Z) ≃ (W ⟶ X * (Y * Z)) :=
  t1.trans (t3.trans t2.symm)

@[simp, reassoc]
lemma homAssocEquiv_natural (k : W' ⟶ W) (f : W ⟶ (X * Y) * Z)
  : homAssocEquiv (W:=W') (k ≫ f) = k ≫ homAssocEquiv (W:=W) f := by
    simp[homAssocEquiv,t1,t2,t3]

def homAssocNatIso {X Y Z : C} : yoneda.obj (((X * Y) * Z)) ≅ yoneda.obj (X * (Y * Z)) :=
  NatIso.ofComponents (fun W => {
    hom := fun f => (homAssocEquiv (W := Opposite.unop W)) f,
    inv := fun g => (homAssocEquiv (W := Opposite.unop W)).symm g,
    hom_inv_id := by
      funext f
      simp,
    inv_hom_id := by
      funext f
      simp
  })
```

The Resuting Associators
===

```lean
def assocIso {X Y Z : C} : ((X * Y) * Z) ≅ (X * (Y * Z)) :=
  (Yoneda.fullyFaithful).preimageIso homAssocNatIso

@[simp]
theorem prod_associator : (assocIso (X := X) (Y:=Y) (Z:=Z)).hom =
                          pair (π₁ ≫ π₁) (pair (π₁ ≫ π₂) π₂) := by
  simp[assocIso,homAssocNatIso,homAssocEquiv,t1,t2,t3,NatIso.ofComponents,Yoneda.fullyFaithful]

@[simp]
theorem prod_associator_inv : (assocIso (X := X) (Y:=Y) (Z:=Z)).inv =
                          pair (pair π₁ (π₂ ≫ π₁)) (π₂ ≫ π₂) := by
  simp[assocIso,homAssocNatIso,homAssocEquiv,t1,t2,t3,NatIso.ofComponents,Yoneda.fullyFaithful]

--hide
```

Conditions for a map to be the Identity
===

The next theorem describes when `f : X * Y ⟶ X * Y` is the identity on `X * Y`.

```lean
-- @[simp]
-- lemma prod_id_unique {f : X * Y ⟶ X * Y} {h₁ : f ≫ π₁ = π₁} {h₂ : f ≫ π₂ = π₂}
--   : f = 𝟙 (X*Y) := by
--     rw[←pair_id,←h₁,←h₂]
--     apply pair_unique
```

Simplifiers for Products
===

```lean
-- @[simp]
-- theorem prod_notation_to_pair {f₁ : Y₁ ⟶ X₁} {f₂ : Y₂ ⟶ X₂}
--    : ‹f₁,f₂› = pair (π₁ ≫ f₁) (π₂ ≫ f₂) := by rfl
```

Theorems About Morphism Products
===

```lean
-- @[simp]
-- theorem prod_map_compf {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : U ⟶ V} {g₂ : V ⟶ W}
--   : ‹ f₁ ≫ f₂, g₁ ≫ g₂ › = ‹ f₁, g₁ › ≫ ‹f₂, g₂› := by simp[←Category.assoc]


-- theorem prod_map_unique {Z X₁ X₂ : C} {g₁ : Z ⟶ X₁} {g₂ : Z ⟶ X₂}
--   {h : Z ⟶ prod X₁ X₂} {h₁ : h ≫ π₁ = g₁} {h₂ : h ≫ π₂ = g₂} :
--   h = pair g₁ g₂ := by
--     rw[←h₁,←h₂]
--     exact pair_unique


-- @[simp]
-- theorem prod_map_id (X Y : C) :
--   (‹𝟙 X, 𝟙 Y› : (X * Y) ⟶ (X * Y)) = 𝟙 (X * Y) := by
--   apply hom_ext
--   · simp
--   · simp

--unhide
```

Example Usage the Associators
===

```lean
lemma fst_fst : (π₁ : (X*Y)*Z ⟶ X*Y) ≫ (π₁ : X*Y ⟶ X) = assocIso.hom ≫ π₁ := by simp

lemma snd_snd : (π₂ : X*(Y*Z) ⟶ Y*Z) ≫ π₂ = assocIso.inv ≫ π₂ := by simp
```

Example: Graphs Have Products
===

Graphs have products called Tensor Products, which we can use to instantiate the `HasProduct` class.

<img src="https://docs.google.com/drawings/d/e/2PACX-1vS8m1ASMsZn0P7p6k0rOGj-8KKBhahoNL7SvrASBquIOwZdxX3_t_49JfFJ7WtowCD-AvSfSe1vkldt/pub?w=814&amp;h=368"
     width=50%>
</img>


```lean
def TensorProd (G H : Graph) : Graph := {
  V := G.V × H.V,
  E := fun (u1,v1) (u2,v2) => G.E u1 u2 ∧ H.E v1 v2
}

--hide
namespace TensorProd
--unhide
```

Example: Tensor Product Properties
===

To form an instance of a `HasProduct` It will be convenient to have the following
properties defined as theorems, which state that products preserve edges.


```lean
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
```

Example: Graphs Have Products
===

Now we can instantiate the `HasProduct` class for graphs. 
```lean
instance Graph.inst_has_product : HasProduct Graph := {
  prod := TensorProd,
  π₁ := fun {X₁ X₂ : Graph} => ⟨ Prod.fst, TensorProd.left ⟩,
  π₂ := fun {X₁ X₂ : Graph} => ⟨ Prod.snd, TensorProd.right⟩,
  pair := fun {X Y Z} f₁ f₂ => ⟨ fun z => ( f₁.map z, f₂.map z ), by
      intro x y h
      exact ⟨ f₁.pe x y h, f₂.pe x y h ⟩
    ⟩
  pair₁ := by intros; rfl
  pair₂ := by intros; rfl
  pair_unique := by
    intro X₁ X₂ Y h
    exact rfl
}

--hide
end HasProduct
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

