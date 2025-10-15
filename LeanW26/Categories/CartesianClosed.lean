import Mathlib
import LeanW26.Categories.Category
import LeanW26.Categories.BinaryProduct
import LeanW26.Categories.Exponential
import LeanW26.Categories.TerminalObject

namespace LeanW26

open CategoryTheory

/-
TODO
===

-/

namespace ReflexiveGraph

class CartesianClosed.{u} (C : Type u) (terminal : C) extends
      Category C, HasProduct C, HasExp C, HasTerminalObject C terminal

instance inst_ccc : CartesianClosed ReflexiveGraph terminus' := {}

-- Do the Category of Equilogical Spaces
--  Obects: (X,~) where X is a topological space and ~ is an equivaence relation
--  Morphisms: Continuous Maps that preserve equivalences

--hide
end ReflexiveGraph
end LeanW26
--unhide
