import Mathlib
import LeanW26.Categories.Category

namespace LeanW26

open CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] {A B U V W W' X X₁ X₂ Y Y₁ Y₂ Z : C}

/-
Yoneda's Lemma
===

This lemma is on of the most fundamental in all of Category Theory. It provides a
way to relate understand objects in a category via their relationships with other objects,
without actually constructing the objects.

- Introduced by Nobuo Yoneda in the 1950s.
- Used by Saunders Mac Lane in his lectures
- Appeared in print in Grothendieck's Bourbaki notes in 1960.

-/

/-
Opposite Categories
===

Given a category `C`, the category `Cᵒᵖ` is defined by
- The same objects as `C`
- Reversed morphisms: If `f : A ⟶ B` in C then `fᵒᵖ : B ⟶ A` in `C`

In Lean, you can use the notation: -/

#check Cᵒᵖ
variable (f : A ⟶ B)
#check f.op

/- Opposite `Cᵒᵖ` has exactly the same data as `C`, and very simple properties, such as -/

example {A B : C} (f : A ⟶ B) : Mono f → Epi f.op := by
  intro h
  simp
  exact h


--hide
end LeanW26
--unide
