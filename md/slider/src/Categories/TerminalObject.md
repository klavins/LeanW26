
Terminal Objects
===

A `terminal object` in Category Theory is an object having a unique morphism from
every other object in that category. We can express this as a type class as follows.

 
```lean
class HasTerminalObject (C : Type*) (T : C) [Category C] where
   term (X : C) : X ⟶ T
   term_unique: ∀ X, ∀ f, f = term X
```

Terminal Objects a Unique up to Isomorhism
===

If a category has multiple terminal objects, then they are all isomorphic.
We use the observation that
```lean
    f ≫ g : T ⟶ T
    id T   : T ⟶ T
```
are both morphisms from `T` to `T` and are thus the same by moprhism uniqueness.
A similar argument holds for `g ≫ f`. Thus, we may conclude
```lean
    f ≫ g = id T
    g ≫ f = id U
```

Uniqueness in Lean
===


```lean
open HasTerminalObject in
theorem terms_are_iso {C : Type*} (T U : C) [Category C]
        [hu : HasTerminalObject C U] [ht : HasTerminalObject C T] :
 ∃ _ : T ≅ U, True := by
   let f := hu.term T
   let g := ht.term U
   use ⟨ f, g,
     by calc f ≫ g
          = term T  := by rw[term_unique T (f ≫ g)]
        _ = 𝟙 T      := by rw[term_unique T (𝟙 T)],
     by calc g ≫ f
          = term U  := by rw[term_unique U (g ≫ f)]
        _ = 𝟙 U      := by rw[term_unique U (𝟙 U)]
    ⟩
```


Terminal Objects in Reflexive Graphs
===

For the Category of Reflexive Graphs, a terminal object is a graph with a single node
and one self edge.


```lean
--hide
namespace ReflexiveGraph
--unhide

def terminus : ReflexiveGraph := ⟨ ⟨ Fin 1, fun _ _ => True ⟩, by exact fun _ => trivial ⟩

instance inst_terminal_object : HasTerminalObject ReflexiveGraph terminus := {

  term := fun G => ⟨ fun v => ⟨ 0, Nat.one_pos ⟩, by
    intro x y h
    exact trivial
   ⟩ ,

  term_unique := by
    intro X ⟨ f, he ⟩
    have : f = (fun v => ⟨ 0, Nat.one_pos ⟩ ) := by
      funext x
      exact Fin.fin_one_eq_zero (f x)
    rw[this]
}
```

Representation Doesn't Matter
===
A result of the the theorem about uniqueness is a graph with one element and one self loop,
no matter how you represent it, is isomorphic to `terminus`.


```lean
def terminus' : ReflexiveGraph := ⟨ ⟨ Unit, fun _ _ => True ⟩, by exact fun _ => trivial ⟩

instance inst_terminal_object' : HasTerminalObject ReflexiveGraph terminus' := {
--brief
  term := fun G => ⟨ fun v => Unit.unit, by
    intro x y h
    exact trivial
   ⟩ ,

  term_unique := by
    intro X ⟨ f, he ⟩
    have : f = (fun v => Unit.unit ) := by
      funext x
      rfl
    rw[this]
--unbrief
}

example : ∃ _ : terminus ≅ terminus', True := by
  exact terms_are_iso terminus terminus'

--hide
end ReflexiveGraph
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

