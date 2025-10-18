
Yoneda's Lemma
===

This lemma is on of the most fundamental in all of Category Theory. It provides a
way to relate understand objects in a category via their relationships with other objects,
without actually constructing the objects.

- Introduced by Nobuo Yoneda in the 1950s.
- Used by Saunders Mac Lane in his lectures
- Appeared in print in Grothendieck's Bourbaki notes in 1960.



Opposite Categories
===

Given a category `C`, the category `Cᵒᵖ` is defined by
- The same objects as `C`
- Reversed morphisms: If `f : A ⟶ B` in C then `fᵒᵖ : B ⟶ A` in `C`

In Lean, you can use the notation: 
```lean
#check Cᵒᵖ
variable (f : A ⟶ B)
#check f.op
```
 Opposite `Cᵒᵖ` has exactly the same data as `C`, and very simple properties, such as 
```lean
example {A B : C} (f : A ⟶ B) : Mono f → Epi f.op := by
  intro h
  simp
  exact h


--hide
end LeanW26
--unide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

