
Beyond Simple Types
===

Is there a non-simply typed λ-calculus? Yes!

- **Simple types** (λ→)Terms depend on terms.
- **Polymorphism** (λ2) Functions can depend on types.
- **Parameterized types** (λ<u>ω</u>) Types can depend on types.
- **Dependent types** (λP) Types can depend on terms.

Putting all of these together you get the **CoC** the **Caclulus of Constructions** (λC),
part of a well-studied framework called the *Lambda Cube*.

<img src="https://upload.wikimedia.org/wikipedia/commons/thumb/c/cd/Lambda_Cube_img.svg/2560px-Lambda_Cube_img.svg.png" width=30%></img>


Adding Inductive Types
===

If we add

- **Inductive Types**: Types are defined with constructors and recursion.

We get **CIC**, the **Calculus of Inductive Constructions**.

Coq, Rocq, and Lean are all loose implementations of CIC.

Lean adds
- Quotients
- Typeclasses
- Universe polymorphism
- Meta programming

Agda is similar, but based on Martin-Löf type theory (MLTT).



Review: Simple Types
===

As described in the previous slide deck, **simple types** consist of `Prop`, `Type u`
and arrow types from `α → β` where `α` and `β` are types.

Terms with these types are
- **Variables** `x : α` where `x` is a symbol and `a` is a type.
- **Abstractions** `fun (x : α) => M x` where
    - `x` is a `bound` variable
    - `α` is a type
    - `M x : β` is a term (usually containing `x`)
- **Applications** `x y : β` where `x : α → β` and `y : α`


Polymorphism
===

**Polymorphism** in Lean is handled the `Π` type formation operator, which
quantifies over types, like `λ` quantifies over terms. For example,

```lean
universe u

def id1 : Π (α : Type u), α → α := fun _ x => x
def id2 : Π {α : Type u}, α → α := fun x => x
def id3 {α : Type u} := fun (x : α) => x
def id4 : (α : Type u) → α → α := fun (_ : Type u) => fun x => x
def id5 : ∀ α, α → α := fun _ => fun x => x
```

Notes:
- `Π` and `∀` are defined as syntactic sugar for `forall`
- `Π` requires Mathlib.
- Regular function types are a special case of Π types.
- The above functions are also **universe polymorphic**


Parameterized types
===

A **parameterized** type has a constructor taking another type as a paramter.

The standard example is List.

```lean
inductive MyList {α : Type} where
  | nil : MyList
  | cons : α → MyList → MyList
```

Note that the constructor for MyList is polymorphic, as one would expect:

```lean
#check MyList.cons    -- {α : Type} → α → MyList → MyList
```

Dependent types
===

A **dependent** type depends on a term. A vector of a given length
is an example. 
```lean
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons {n} :  α → Vec α n → Vec α (n + 1)
```

Here is a polymorphic function that adds two vectors together.

```lean
def Vec.add {α : Type u} [Add α] {n : Nat} (x y : Vec α n)
  : Vec α n :=
  match x, y with
  | nil, nil => nil
  | cons a w, cons b z => cons (a+b) (Vec.add w z)
```
 The notation [Add α] ensures that α is a type that has addition (See Typeclasses)
```lean
#check_failure Vec.add (Vec.nil.cons 1) ((Vec.nil.cons 1).cons 2)
```

Exercises
===

<ex/> Define a parameterized structure type called `Pair` that represents a
pair of values having not necessarily the same types.

<ex/> Define a polymorphic function that swaps the order of a `Pair`. What is
it's type?

<ex/> Consider the dependent type


```lean
def chooseType : Bool → Type
| true  => Nat
| false => String
```
 Create a function `f : Bool → chooseType Bool`. 

Sigma Types
===

A Sigma type is
parameterized (by `α` and `β`), polymorphic (via the type of `β`),
and dependent (via the constructor for `snd`). In Lean, Sigma is defined by
```lean
structure Sigma {α : Type u} (β : α → Type v) where
  fst : α
  snd : β fst
```
For example, to carry around a length and a default vector of that
length, we could do:


```lean
#check Sigma.mk 0 Vec.nil
#check Sigma.mk 1 (Vec.nil.cons 0)
```

A Function on Sigma Types
===

Lean provides the notation `Σ` for Sigma types.

```lean
def Vec.default (n : Nat) : Σ (n:Nat), Vec Nat n := match n with
  | 0 => Sigma.mk 0 Vec.nil
  | n+1 => let v := (Vec.default n)
           Sigma.mk (v.fst+1) (v.snd.cons 0)

#check Vec.default 3 --- (n : ℕ) × Vec ℕ n
```

Exercises
===

<ex /> Define a function
```lean
forget : Σ (n:Nat), Vec Nat n → List Nat
```
that takes a Sigma value representing a length and a vector of that length
and returns the vector turned into a list.



Various Advanced Types (Not in Lean)
===

**Univalence**: In mathematics, we often reason about objects *up to isomorphism*.
The *univalence axiom* says `A ≃ B → A = B`, meaning once you prove an isomorphism,
you get equality. In lean, you do this in a clunk way with quotient.

**Higher Inductive Types**: Point constructors and path constructors.

**HOTT**: Types are spaces, equalities are paths between
equal objects. Equalities of equalities are higher order paths.
 Univalence + Inductive types with a homotopy interpretation of
types as spaces, terms as points, and equalities as maths.
Very elegant math, but decidability issues abound.

**Cubical Types**: Introduces an interval object `I = [0,1]` and cubes made from it.
Path types are `I → Type`. Makes (requires) HITs to be constructive. Makes
type checking decidable.

**Many Others**: Observational type theory, modal type theory, linear type theory, ...








References
===

- Thierry Coquand and Gérard Huet, The Calculus of Constructions, *Information and Computation*,
Vol. 76, Issue 2, pp. 95–120, 1988.
- Thierry Coquand and Christine Paulin, Inductively Defined Types, in COLOG-88: International
Conference on Computer Logic, *Lecture Notes in Computer Science*, vol. 417, Springer, 1988. 
```lean
end LeanW26.NonSimpleTypes
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

