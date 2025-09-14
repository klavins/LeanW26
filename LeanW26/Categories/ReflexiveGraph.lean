import Mathlib
import LeanW26.Categories.CartesianClosed
import LeanW26.Categories.Graph

namespace LeanW26

open CategoryTheory

/- # Reflexive Graphs: A Subcategory of Graphs

To show an example of exponentials, we can't use simple graphs, as we need self-loops.
We can build a subcategory of Graph called ReflexiveGraph that does this using
Mathlib's `FullSubcategory` helper. -/

def ReflexiveGraph.{u} : Type (u+1) :=
  ObjectProperty.FullSubcategory (fun G : Graph.{u} => ∀ v, G.E v v)

namespace ReflexiveGraph

/- We can then show ReflexiveGraph is also a category and that it has products. -/

instance inst_category.{u} : Category ReflexiveGraph.{u} :=
  ObjectProperty.FullSubcategory.category _

/- For the product instance, it would be nice if there were a way to just use the
fact that Graphs have products. Or at least use some of that proof. But I could not
figure that out so this is mostly just repetetive at this point. -/

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

/- # Reflexive Graphs Have Exponentials

Here's a paper with something like this construction:

  https://arxiv.org/pdf/1807.09345

The exponential G^H is the graph in which the vertices are morphisms from H to G,
and the edges are the "natural transformations". The transformation maps vertices
and edges of G to those of H in a way that commutes.

First we define the exponential object of two Reflexive Graphs. Note the universe
condition. We need to have the exponential object like in a higher universe
otherwise we get Russel's paradox issues. -/

def exp.{u} (G H : ReflexiveGraph.{u}) : ReflexiveGraph.{u} := {
  obj := {
    V := ULift.{u} (H ⟶ G),
    E := fun F₁ F₂ =>
      let f₁ := ULift.down F₁
      let f₂ := ULift.down F₂
      ∀ u v : H.obj.V, H.obj.E u v → G.obj.E (f₁.f u) (f₂.f v)
  },
  property := by
    intro morphism u v h
    exact morphism.down.pe u v h
}

/- The eval function is straighforward. -/

def eval (H G : ReflexiveGraph) : HasProduct.prod (exp H G) G ⟶ H := {
    f := fun ⟨ ⟨ f, h ⟩, v  ⟩ => f v,
    pe := by
      intro ⟨ ⟨ fg, hfg ⟩, vG ⟩ ⟨ ⟨ fh, hfh ⟩, fH ⟩ ⟨ h1, h2 ⟩
      simp_all only[exp]
}

/- And now we can instantiate HasExp. -/

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

  curry_eval := by
    intros
    rfl,

  curry_unique := by
    intro _ _ _ _ _ comm
    rw[←comm]
    rfl

}

/- Hooray! -/

#check CategoryTheory.Limits.hasTerminal_of_unique

end ReflexiveGraph

end LeanW26
