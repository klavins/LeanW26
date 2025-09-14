def hello := "world"

def identity {α : Type} (x : α) : α := x
-- The type of `identity` is `∀ α : Type, α → α`
#check identity
