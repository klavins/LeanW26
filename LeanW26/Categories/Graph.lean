import Mathlib
import LeanW26.Categories.CartesianClosed

open CategoryTheory

namespace LeanW26

/-
Example: Graphs
===

Graphs form a category, and they have products (the so-called Tensor Products).
First we define a simple directed graph class. -/

class Graph.{u} where
  V : Type u
  E : V → V → Prop

namespace Graph

/-
Graph Morphisms
===

A morphism relating two graphs `G` and `H` is required to preserve the edge relationship.
 -/

@[ext]
structure Hom (G H : Graph) where
  f : G.V → H.V
  pe: ∀ x y, G.E x y → H.E (f x) (f y)

/- With the notion of a `Graph` morphism defined, we can instantiate the `quiver` class, which
allows us to write `G ⟶ H` for our morphisms. -/

instance inst_quiver : Quiver Graph := ⟨
  fun G H => Hom G H
⟩

/- Note that in Lean, the class `Category` extends the class `Quiver`.


Example
===

As an example, here are two graphs:

<img src="/img/graph-morphism.svg" style="height:20%;"/>

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
Graphs Form a Category
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

/- And showing graphs are a category is now easy. -/

instance inst_category : Category Graph := {
  id := id_hom,
  comp := comp_hom,
  id_comp := by aesop,
  comp_id := by aesop,
  assoc := by aesop
}

/- Now we can compose graph homomorphisms. Here f ≫ g means apply f, then apply g.
That is, it is notation for comp g f. -/

#check f ≫ (id_hom G2)
#check (id_hom G1) ≫ f
#check (id_hom G1) ≫ f ≫ (id_hom G2)

example : (id_hom G1) ≫ f = f := by rfl
example : f ≫ (id_hom G2) = f := by rfl
example : ((id_hom G1) ≫ f) ≫ (id_hom G2) = (id_hom G1) ≫ (f ≫ (id_hom G2)) := by rfl

end Graph

/- # Graphs Have Products

Graphs have products called TensorProducts, which we can use to instantiate the `HasProduct` class.

-/

def TensorProd (G H : Graph) : Graph := {
  V := G.V × H.V,
  E := fun (g1,h1) (g2,h2) => G.E g1 g2 ∧ H.E h1 h2
}

namespace TensorProd

theorem left {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → G.E x.1 y.1 := by
  intro x y h
  exact h.left

theorem right {G H : Graph} :
  ∀ x y, (TensorProd G H).E x y → H.E x.2 y.2 := by
  intro x y h
  exact h.right

end TensorProd

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
    rw[← h1, ← h2]
    rfl

}

end LeanW26
