
Ontologies
===


Definition
===

Def: **Ontology** A set of concepts and categories in a subject area or domain that shows their properties and the relations between them.

Concepts of interest: Events, Time, Physical Objects, Beliefs


For example, an ontology may be structured like this:

<div style="font-size: 10pt">
```none
                  ———————————————Anything————————————————
                /                                         \
AbstractObjects ——————                          ——————GeneralizedEvents
  |       \            \                       /         |        |      \
Sets    Numbers   RepresentationalObjects   Intervals  Places  Objects Processes
  |                       /       \           |          |        |
Categories             Times     Weights    Moments    Things   Stuff —————
                                                     /    |     /   \       \
                                              Animals  Agents  Solid Liquid Gas
                                                  \     /
                                                  Humans
```
</div>

<div class='fn'>Russel and Norvig, Introduction to Artificial Intelligence 3rd Ed, p 315.</div>


Examples
===

- [Cyc](https://cyc.com/): Hand coded for deep logical reasoning. 40K predicates, 1.5M concepts, 25M axioms.

- [Wikidata](https://query.wikidata.org/) : Try it!


- [Google Knowledge Graph](https://developers.google.com/knowledge-graph):
Automatically extracted from the web for search apps.
54 billion entities, 1.6 trillion facts.
Powers _Knowledge Panels_, for example.

- [The Gene Ontology Resource](https://geneontology.org/) : Example of a domain specific ontology


Example GKG Query
===

You can go to the Google KG and search for "Taylor Swift". Among other bits of information, Google will return
<div style="font-size: 10pt">
```none
        ...
        "@id": "kg:/m/0dl567",
        "name": "Taylor Swift",
        "@type": [
          "Thing",
          "Person"
        ],
        "description": "Singer-songwriter",
        ...
```
</div>

Good to know!

Ontologies in FOL
===

Goal: Represent ontologies of this with FOL, even though FOL is fairly limited for representing real world knowledge. For example,
```none
  ∀ x , Tomato(x) → Red(x)
```
is not always true. Listing all the exceptions to a rule is an area of research.


Categories and Objects
===

To reason about objects, doing so at the level of categories of objects is preferred.
For example, we might want to state a property about all basketballs or all balls,
rather than about each specific ball.

Here we'll use the word `category` to be consistent with Russel and Norvig,
not be confused with the mathematical notion of a category. 
```lean
universe u

def Category (α : Type u) := α → Prop
```
 Now we can introduce categories and state that an object is in a category. 
```lean
variable (base : Type u)
         (b : base)
         (Basketball: Category base)
         (m1 : Basketball b)
```

Sub-categories
===

We can express what it means to be a sub-category. 
```lean
def Subcategory {α : Type u} (A : Category α) (B : Category α) :=
  ∀ x : α , A x → B x
```
 Now we can do a simple example. 
```lean
example (Object : Type) (b : Object) (Basketball Ball: Category Object) :
  Basketball b ∧ Subcategory Basketball Ball → Ball b := by
  intro ⟨ h1, h2 ⟩
  apply (h2 b) h1
```

Numerical Functions
===

This type allows us to write all of the statements in the first section of Russel and Norvig's chapter on knowledge representation. 
```lean
def NumericalFunction (α : Type u) := α → Float

variable (base : Type u)
         (b c : base)
         (Basketball Ball Spherical Orange Round: Category base)
         (Diameter : NumericalFunction base)
         (m1 : Basketball b)
         (s3 : Subcategory Basketball Orange)
         (s1 : Subcategory Basketball Ball)
         (s2 : Subcategory Ball Spherical)
         (f1 : ∀ x, Basketball x → Diameter x = 9.5)
         (r1 : ∀ x, Orange x ∧ Round x ∧ Diameter x = 9.5 ∧ Ball x → Basketball x)

example : Ball b := s1 b m1
example : Spherical b := s2 b (s1 b m1)
example : Orange b := s3 b m1
```

Categories of Categories
===

An entire category can be a member of a sort of meta category. For example, 
```lean
def MetaCategory (α : Type u) := Category α → Prop

variable (DomesticatedSpecies Animals: MetaCategory base)
         (Dogs Cats: Category base)
         (c1 : DomesticatedSpecies Dogs)
         (c2 : DomesticatedSpecies Cats)
         (s4 : Subcategory DomesticatedSpecies Animals)
```
 These types of relationships would allow you to reason at a meta level about categories.
An infinite hierarchy of categories is essentially what Lean's universe and type system allows,
suggesting how this might be used. 

Disjoint Pairs
===

Knowledge bases often describe what objects are not.
One way to do this is to add a requirement that two categories have no objects in common.


```lean
def DisjointPair {α : Type u} (A: Category α) (B: Category α) :=
  ∀ x : α , (A x → ¬B x) ∧ (B x → ¬A x)

variable (Animal Vegetable : Category base)
         (d1: DisjointPair Animal Vegetable)

example (x : base) : Animal x → ¬ Vegetable x := by
  intro h
  have ⟨ hl, _ ⟩ := d1 x
  apply hl h
```

Disjoint Lists
===

You might describe a fully disjoint list of categories. Here, we use Lean's `List` type.


```lean
def Disjoint {α : Type u} (parts : List (Category α)) :=
  List.Pairwise DisjointPair parts

variable (Mineral : Category base)
         (d2: Disjoint [Animal, Vegetable, Mineral])

example (x : base): Animal x → ¬ Vegetable x ∧ ¬ Mineral x := by
  intro h
  have h0 := d2
  simp[Disjoint, DisjointPair] at h0
  have ⟨ ⟨ h1, h2 ⟩, _ ⟩ := h0
  have ⟨ h4, _ ⟩ := h1 x
  have h5 := h4 h
  have ⟨ h6, _ ⟩ := h2 x
  have h7 := h6 h
  apply And.intro h5 h7


-- A condensed proof
example : ∀ (x : base) , Animal x → ¬ Vegetable x ∧ ¬ Mineral x := by
  intro x h
  simp[Disjoint] at d2
  exact ⟨ (d2.left.left x).left h, (d2.left.right x).left h ⟩
```

Exhaustive Categories

Prescribing an exhaustive set of categories disallows an object from not belonging to *some* category.
The definition does not require that an object is in only one category.
In the example below, one might have a dual citizenship.


 A helper function that returns whether P is true for some object in a list L. 
```lean
def exists_in_list {α : Type u} (L : List α) (P: α → Prop) := match L with
  | [] => False
  | h :: t => P h ∨ exists_in_list t P

def ExhaustiveDecomposition {α : Type u} (parts : List (Category α)) (whole: Category α) :=
  ∀ (x : α) , (whole x) ↔ (exists_in_list parts (λ p => p x))

variable
  (American Canadian Mexican NorthAmerican : Category base)
  (ed1 : ExhaustiveDecomposition [American, Canadian, Mexican] NorthAmerican)

example (x : base) :   NorthAmerican x
                   ∧ ¬ Canadian x
                   ∧ ¬ Mexican x → American x:= by
  intro ⟨ h, hs, hl ⟩
  have h0 := (ed1 x).mp h
  iterate 4 rw[exists_in_list] at h0
  simp[*] at h0
  exact h0
```

Partitions
===

A partition is a set of categories that is disjoint and exhaustive.


```lean
def Partition {α : Type u} (parts : List (Category α)) (whole: Category α) :=
  ExhaustiveDecomposition parts whole ∧ Disjoint parts

variable (Student UG Masters PHD : Category base)
variable (p1 : Partition [UG, Masters, PHD] Student)
```
 This next example dones't use the disjoint part 
```lean
example (x : base) : Student x ∧ ¬ UG x ∧ ¬ Masters x → PHD x := by
  intro ⟨ hs, hug, hms ⟩
  have h0 := (p1.left x).mp hs
  simp[exists_in_list] at h0
  cases h0 with
  | inl h2 => exact False.elim (hug h2)
  | inr h3 => cases h3 with
    | inl h4 => exact False.elim (hms h4)
    | inr h5 => exact h5

#check not_or_intro
```
 This example doesn't use the exhaustive part.  
```lean
example (x : base) : PHD x → ¬(UG x ∨ Masters x) := by
  intro h
  have h1 := p1.right
  simp[Disjoint,DisjointPair] at h1
  have ⟨ ⟨ _, g2 ⟩, g3 ⟩ := h1
  exact not_or_intro ((g2 x).right h) ((g3 x).right h)
```
 This part uses the reverse of the condition in Exhaustive Decomposition 
```lean
example (x : base) : PHD x → Student x := by
  intro h
  have h0 := (p1.left x).mpr
  simp[exists_in_list] at h0
  exact h0 (Or.inr (Or.inr h))
```

Definitions
===

One can simply state that an object is in a category, or one can define
what the category is by relating it to other categories. Here's an example.


```lean
variable (Bachelor Unmarried Adult Male : Category base)
         (def_bachelor : ∀ (x:base), Bachelor x ↔ Unmarried x ∧ Adult x ∧ Male x)

example : ∀ (x:base) , Bachelor x → Male x := by
  intro x h
  have ⟨ _, _, hm ⟩ := (def_bachelor x).mp h
  exact hm
```

Physical Composition
===

```lean
def Relation (α : Type u) := α → α → Prop
def Reflexive (r : Relation α)  := ∀ a : α , r a a
def Transitive {α : Type u} (r : Relation α) :=
  ∀ x y z , r x y → r y z → r x z

variable (PartOf : Relation base)
         (part_of_refl  : Reflexive PartOf)
         (part_of_trans : Transitive PartOf)

variable (Bucharest Romania EasternEurope Europe Earth : base)
         (pbr : PartOf Bucharest Romania)
         (pree : PartOf Romania EasternEurope)
         (peee : PartOf EasternEurope Europe)
         (pee : PartOf Europe Earth)

example : PartOf Bucharest Earth := by
  have h1 := part_of_trans Bucharest Romania EasternEurope
  have h2 := part_of_trans Bucharest EasternEurope Europe
  have h3 := part_of_trans Bucharest Europe Earth
  exact h3 (h2 (h1 pbr pree) peee) pee
```

Object Construction
===

Below we state that if an animal is a biped, then it has exactly two legs that are attached to its body.

 
```lean
variable (Leg Body Biped : Category base)
         (Attached : Relation base)
         (attached_refl : Reflexive Attached)

variable (is_biped : ∀ a , Biped a →
  ∃ l₁ l₂ b , Leg l₁ ∧ Leg l₂ ∧ Body b ∧
              PartOf l₁ a ∧ PartOf l₂ a ∧ PartOf b a ∧
              Attached l₁ b ∧ Attached l₂ b ∧
              l₁ ≠ l₂ ∧
              ∀ l₃ , Leg l₃ ∧ PartOf l₃ a → (l₃ = l₁ ∨ l₃ = l₂))
```

Related Concepts
===

- The mass of a composite object is the sum of the masses of its parts
- BunchOf : List Category base → Category base, for example a bunch of apples
- ∀ x , S x → PartOf(s,BunchOf(S))



License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

