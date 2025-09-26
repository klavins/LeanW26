theorem t1 {p q : Prop} : (p → q) → (p → q) := by
  intro h1
  intro h2
  have := h1 h2
  exact this

theorem t2 {p q : Prop} : p ∧ q → p ∧ q := by
  intro h
  apply And.intro
  . exact h.left
  . exact h.right
