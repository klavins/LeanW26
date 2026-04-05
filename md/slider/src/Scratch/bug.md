
<div class="lean-code" data-start-line="1" data-end-line="27"><pre><code>import Mathlib

universe u
variable {α : Type u}

def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n &gt; m, σ₁ n = σ₂ n

instance te_equiv {α : Type u} : Equivalence (te (α := α)) := {
  refl x := ⟨ 0, fun _ _ =&gt; rfl ⟩,
  symm {x y} := fun ⟨ m,h ⟩ =&gt; ⟨ m, by aesop ⟩,
  trans {x y z} := fun ⟨ m₁, h₁ ⟩ =&gt; fun ⟨ m₂, h₂ ⟩ =&gt; ⟨ m₁ ⊔ m₂, by aesop ⟩
}

instance te_setoid {α : Type u} : Setoid (ℕ → α) := {
  r := te,
  iseqv := te_equiv
}

def respects {α : Type u} [Setoid α] (f : α → α) := ∀ x y, x ≈ y → f x ≈ f y

def pre_neg {α : Type u} [hn : Neg α] (σ : ℕ → α) : ℕ → α := fun n =&gt; -(σ n)

theorem te_neg_respects {α : Type u} [Neg α] : respects (α := ℕ → α) pre_neg := by
  intro σ τ ⟨ m, h ⟩
  use m
  simp[pre_neg]
  aesop</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

