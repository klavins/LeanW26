
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Appendix.lean'>Code</a> for this chapter</span>
 # Useful Theorems 
```lean
theorem not_empty_to_exists {A : Type u} {S : Set A} : S ≠ ∅ → ∃ x, x ∈ S := by
   intro h
   by_contra h'
   simp at h'
   exact h (Set.eq_empty_iff_forall_not_mem.mpr h')

theorem not_full_to_not_exists {A : Type u} {S : Set A}
  : S ≠ Set.univ → ∃ x, x ∉ S := by
  intro h
  exact (Set.ne_univ_iff_exists_not_mem S).mp h

theorem not_empty_set_diff {A : Type u} {X Y : Set A} (h : ¬X ⊆ Y)
  : X \ Y ≠ ∅ := by
  simp[Set.instSDiff,Set.diff]
  by_contra hx
  simp at hx
  exact h hx

theorem remove_set_notation {T : Type*} (A : Set T) (f : T → Prop)
  : { x | f x } = A ↔ ∀ x, x ∈ A ↔ f x := by
  constructor
  . exact fun a x ↦ Iff.symm (Eq.to_iff (congrFun a x))
  . exact fun a ↦ Eq.symm (Set.ext a)
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
