
Reflexive Graphs
===

```lean
-- namespace ReflexiveGraph
-- class CartesianClosed.{u} (C : Type u) (terminal : C) extends
--       Category C, HasProduct C, HasExp C, HasTerminalObject C terminal
-- instance inst_ccc : CartesianClosed ReflexiveGraph terminus' := {}
-- end ReflexiveGraph
```

Equilogical Spaces
===

```lean
universe u v
variable {X : Type u} [TopologicalSpace X] {r : X → X → Prop}

class Equ where
  X : Type u
  r : X → X → Prop
  [is_top : TopologicalSpace X]
  is_equiv : Equivalence r

attribute [instance] Equ.is_top

open CategoryTheory

@[ext]
structure Equ.Hom (A B : Equ) : Type u where
  map : A.X → B.X
  is_continuous : @Continuous A.X B.X A.is_top B.is_top map
  respects_eq : ∀ x y : A.X, A.r x y → B.r (map x) (map y)

instance equ_quiver_inst : Quiver Equ := ⟨ Equ.Hom ⟩

def Equ.id_hom (E : Equ) : E ⟶ E := {
      map := fun x => x,
      is_continuous := @continuous_id E.X E.is_top,
      respects_eq := by
            intros x y h
            exact h
}

def Equ.comp {G H I : Equ} (f : G ⟶ H) (g : H ⟶ I) : G ⟶ I := {
  map := g.map ∘ f.map,
  is_continuous := by
    exact @Continuous.comp G.X H.X I.X G.is_top H.is_top I.is_top
                           f.map g.map g.is_continuous f.is_continuous
  respects_eq := by
      intros x y h
      have hf := f.respects_eq x y h
      have hg := g.respects_eq (f.map x) (f.map y) hf
      exact hg
}

instance Equ.cat_inst : Category.{u,u+1} Equ := {
      Hom := Hom,
      id := Equ.id_hom,
      comp := Equ.comp
}

def Equ.prod_r {G H : Equ} (a b : G.X × H.X) := G.r a.1 b.1 ∧ H.r a.2 b.2

theorem Equ.prod_r_equiv {G H : Equ} : @_root_.Equivalence (G.X × H.X) Equ.prod_r := by
    exact {
        refl := by
          intro (x,y)
          exact ⟨ G.is_equiv.refl x, H.is_equiv.refl y⟩
        symm := by
          intro (w,x) (y,z) ⟨ h1, h2 ⟩
          exact ⟨ G.is_equiv.symm h1, H.is_equiv.symm h2 ⟩
        trans := by
          intro (u,v) (w,x) (y,z) ⟨ h1, h2 ⟩ ⟨ h3, h4 ⟩
          exact ⟨ G.is_equiv.trans h1 h3, H.is_equiv.trans h2 h4 ⟩
    }

def Equ.prod (G H : Equ.{u}) : Equ.{u} := {
      X := G.X × H.X,
      r := Equ.prod_r,
      is_top := by exact instTopologicalSpaceProd,
      is_equiv := Equ.prod_r_equiv
}

def Equ.fst {F G} : Equ.prod F G ⟶ F := {
      map := Prod.fst,
      is_continuous := by
        simp[Equ.prod,continuous_fst],
      respects_eq := by
        intro F G ⟨ h1, _ ⟩
        exact h1
}

def Equ.snd {F G} : Equ.prod F G ⟶ G := {
      map := Prod.snd,
      is_continuous := by
        simp[Equ.prod,continuous_snd],
      respects_eq := by
        intro F G ⟨ _, h2 ⟩
        exact h2
}

def Equ.pair {F G H : Equ} (f : H ⟶ F) (g : H ⟶ G) : H ⟶ Equ.prod F G :=
  {
    map := fun X => (f.map X, g.map X),
    is_continuous := by
      exact (continuous_prodMk.mpr ⟨f.is_continuous, g.is_continuous⟩)
    respects_eq := by
      intro x y h
      exact ⟨ f.respects_eq x y h, g.respects_eq x y h ⟩
  }

instance Equ.has_product_inst : HasProduct.{u+1,u} Equ := {
      prod := Equ.prod,
      π₁ := (Equ.fst : ∀ {X₁ X₂ : Equ}, (Equ.prod X₁ X₂) ⟶ X₁),
      π₂ := (Equ.snd : ∀ {X₁ X₂ : Equ}, (Equ.prod X₁ X₂) ⟶ X₂),
      pair := (fun {X₁ X₂ Y} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) => pair f₁ f₂)
}
```

Example: S₁
===

```lean
def point : Equ := {
  X := Unit,
  r := fun x y => True,
  is_equiv := {
    refl := by aesop,
    symm := by aesop,
    trans := by aesop
  }
}

def S1 : Equ := {
  X := ℝ,
  r := fun x y => ∃ k : ℤ, y-x = k,
  is_equiv := by
    exact {
      refl := by
        intro x
        use 0
        simp,
      symm := by
        intro x y ⟨ k, h ⟩
        use -k
        simp
        linarith,
      trans := by
        intro x y z ⟨ k₁, h₁ ⟩ ⟨ k₂, h₂ ⟩
        use k₁+k₂
        simp
        linarith
    }
}

def T2 : Equ := Equ.prod S1 S1

def T (n : Nat) : Equ := match n with
  | Nat.zero => point
  | Nat.succ k => Equ.prod S1 (T k)

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

