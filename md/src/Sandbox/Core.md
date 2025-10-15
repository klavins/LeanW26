 Note that X × Y is not really And, because it does not have type Prop.
--   
```lean
-- example : (A × (A → B)) → B := by
--   intro h
--   exact h.2 h.1

universe u v w

set_option linter.missingDocs false

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit

inductive True : Prop where
  | intro : True

inductive False : Prop

def Not (a : Prop) : Prop := a → False

-- structure And (a b : Prop) : Prop where
--   intro ::
--   left : a
--   right : b


structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

structure MProd (α β : Type u) where
  fst : α
  snd : β


set_option autoImplicit false


inductive And (p q : Prop) : Prop where
  | intro : p → q → (And p q)

def And.left {p q : Prop} (hpq : And p q) : p :=
  And.rec (fun hp _ => hp) hpq

def And.right {p q : Prop} (hpq : And p q) : q :=
  And.rec (fun _ hq => hq) hpq

example : Type 2 := Type 1

example (p : Prop) : Prop := p

example (p q : Prop) : (And p (p → q)) → q :=
  fun hpq => hpq.right hpq.left

-- example : ∀ x : A, A := sorry

example {f : A → Type} {b : Type} : Π x : A, A × A := by
  intro x
  exact (x,x)
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

