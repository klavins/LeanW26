
Russell's Paradox
===

Let `S` be the set of all sets that are not members of themselves.

If `S ∈ S` then by definition `S ∉ S`.

If `S ∉ S` then by definition `S ∈ S`.

Set Theory, this is avoided by only allowing set definitions
to refer only to existing sets.



Girard's Paradox
===

Similarly, if you allow type definitions to quantify over all types (including
themselves), you end up with a paradox.

Allowing quantification over the thing being defined is called *Impredicativity*.

Most type theories disallow impredicativity for general types, but does allow it for a
special type `Prop`, as we shall see.



Universe Hierarchy
===

Lean, and most Type Theories, define a hierarchy of universes

    - Sort 0 = Prop
    - Sort 1 = Type 0 = Type
    - Sort 2 = Type 1
    ...

All types have types:

    - Prop : Sort 0          (read: Prop "has type" Sort 0)
    - Type u : Type u+1

Now expressions don't quantify over all types,
they quantify over types in lower universe levels.

Types in Lean
===

You can use `#check` to check types

```lean
#check Prop            -- Type

#check Type            -- Type 1
#check Type 0          -- Type 1

#check Type 12         -- Type 13

#check_failure Type 100 -- Universe level offset `100`
                        -- exceeds maximum offset `32`
```

Universe Variables
===

You can declare universes with the universe command:

```lean
universe u v
def f1 (x : Type u) : Type u := x
```
 Or you can use the dot notation 
```lean
def f2.{w} (x : Type w) : Type w := x
```

The function is then *universe polymorphic*

```lean
#check f2                         -- Type v → Type v
#check f2 Nat                     -- Type (since Nat : Type)
#check f2 (List (Type 0))         -- Type 1, since Lists of type can't have their
                                  -- own types as elements
```

Self Application Does not Work
===

You can't apply `f2` to itself: 
```lean
#check_failure f2 f2
```
 Gives

```lean
Application type mismatch: The argument
  f2
has type
  Type ?u.27 → Type ?u.27
but is expected to have type
  Type ?u.27
in the application
  f2 f2
```


Function Types
===
Functions have type `Type u → Type v` for some universe levels `u` and `v`.

```lean
def my_id (x : Type u) := x

#check my_id             -- Type → Type
#check my_id String      -- Type → Type
```

Since `Type → Type` is a type, it must have a type. 
```lean
#check Type → Type       -- Type 1
```

If the type of `Type → Type` were `Type`, then `Type` would contain a function
whose domain and codomain are both `Type`, meaning it would contain an element
that refers to itself.


Type Arithmetic
===

You can
- Add natural numbers to universes
- Take the max of two universes


```lean
#check Type (u+1)
#check Type (max u v)
```
 For example 
```lean
#check Prod             -- Type u → Type v → Type (max u v)
#check Type u × Type v  --  Type (max (u + 1) (v + 1))
```
 There is also:
```lean
imax u v := if u = 0 then 0 else max u v
```

```lean
#check Type (imax 1 0)   -- 0
#check Type (imax 0 1)   -- 1
```

Prop is Impredicative
===

Generally you cannot have a type built from other types live in the same unvierse level.

For example, if you change `u+1` to `u` below, you get a type error.


```lean
def MyProd (α β : Type u) : Type (u+1) :=
  Π X : Type u, (α → β → X) → X
```

However, with `Prop` you *ca*n make such definitions.

```lean
def MyPropProd (α β : Prop) : Prop :=
  ∀ X : Prop, (α → β → X) → X
```
 This is because `Prop` is impredicative in Lean, unlike all other types. 

How `Prop` Avoids Paradoxes
===

Even though `Prop` is impredicative, the language is carefully designed to avoid
allowing paradoxes.

This is achieved via ***proof irrelevance***: All proofs `h : p` where `p : Prop` are equivalent.

The result is that propositions cannot depend on the particular way a proof is written,
and so lack the expressive power to encode Girard's paradox.



References
===

Universe hierarchies appear to have been introduced by Per Martin-Löf in

> Per Martin-Löf, An Intuitionistic Theory of Types: Predicative Part,
*Studies in Logic and the Foundations of Mathematics*, Volume 80, 1975, Pages 73-118. [Link](https://www.sciencedirect.com/science/chapter/bookseries/abs/pii/S0049237X08719451)



Exercises
===

<ex/> What is the type of `Type u × Type v`?

<ex/> Define
```lean
def TypeList := List Type
```
Which of the following are ok in Lean? Why?
```
def A : TypeList := []
def A : TypeList := [ℕ,ℚ]
def A : TypeList := [ℕ,List ℕ]
def A : TypeList := [ℕ,A]
```

<ex/> Why doesn't this function type check?
```lean
def f (n : ℕ) := if n = 0 then Type 0 else Type 1
```


```lean
--hide
end LeanW26.Universes
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

