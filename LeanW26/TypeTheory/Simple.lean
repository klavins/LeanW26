import Mathlib

namespace LeanW26

/-
Type Universes
===

Arrow Types
===
-/

#check (1,1)
#print Prod

-- Good explanation: https://www.youtube.com/watch?v=mTwvecBthpQ at 1:28:00

-- Simple : Just arrows, simple sums and products
-- But products are structures
#check fun x : Type => x
#check Type × Type
#check Type ⊕ Type
#check fun x : Type => (x,x)
#check fun x : Type => (Sum.inl x : Type ⊕ Type)

-- Inductive Types could go here

-- Polymorphic : Can have types as arguments or parameters
#check fun a : Type => fun x : a => x

-- Dependent : Can quantify over types
#check (x:Int) → x > 1
#check Π (x:Int), x > 1
#check ∀ (x:Int), x > 2
#check Σ (x:Nat), Fin (x+2)

-- Types on Types
def Option (α : Type) : Type := α ⊕ Unit



end LeanW26
