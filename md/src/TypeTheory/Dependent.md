
Todo
===

    - Π x : T, M x
    - ∀ x : T, P x
    - Arrow types are actually a special case of dependent types
    - Gives you parametric polymoprhism

Todo
===

```lean
-- A type-level function that is universe polymorphic
def Pair.{u, v} (α : Type u) (β : Type v) : Type (max u v) :=
  Prod α β

#check Pair Nat Bool          -- Type
#check List Nat
#check Pair (List Nat) Nat      -- Type 1



def Compose.{u, v, w}
    (F : Type v → Type w) (G : Type u → Type v) : Type u → Type w :=
  fun α => F (G α)

#check Compose Option List Nat  -- Option (List Nat)


def Arrow.{u, v} (α : Type u) (β : Type v) : Type (max u v) :=
  α → β

#check Arrow Nat Bool        -- Nat → Bool : Type
#check Arrow (List Nat) Nat    -- (Type 0) → Nat : Type 1


def Compose2.{u, v, w}
    (F : Type v → Type w) (G : Type u → Type v) : Type u → Type w :=
  fun α => F (G α)

#check Compose2 Option List Nat  -- Option (List Nat)

end LeanW26
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

