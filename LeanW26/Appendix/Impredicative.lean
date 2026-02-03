section
  def Set (α : Type):= α → Prop
  variable (α : Type) (A B : Set α)
  #check (x : α) → A x → B x -- Prop, no universe bump
end

section
  def Bet (α : Type) := α → Type
  variable (α : Type) (A B : Bet α)
  #check Type → Type         -- Type 1
  #check ∀ x : α,  A x → B x -- Type
end


/-
For types, the universe rule is

  Π(x:Type u),Type v:Type(max(u,v))

for Prop it is

  Π(x:Sort u),Prop:Prop


-/
