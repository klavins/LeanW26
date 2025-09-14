
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Strings.lean'>Code</a> for this chapter</span>
 # Strings 
```lean
open List
```
 **Note** that List already have an ordering on them, but it is not the prefix ordering.
   This creates issues because List.le and [LT (List A)] are already defined. We avoid this
   here by just not using the ≤ notation.  
```lean
#check List.le
variable {A : Type u} (x : List A) [LT A]
#check [] ≤ x
#eval [1,2,3] ≤ [1,2,5]
example {A : Type u} [LT A] (x : List A) : [] ≤ x := by
  simp[List.instLE]
```
 **End Note** 
```lean
instance list_poset {A : Type u} : Poset (List A) :=
  ⟨
    IsPrefix,
    List.prefix_refl,
    by
      intro s t ⟨ x, h1 ⟩ ⟨ y, h2 ⟩
      aesop,
    by
      intro s t u
      exact List.IsPrefix.trans
  ⟩

example {A : Type u} (x : List A) : [] <+: x := by
  simp[list_poset]

def meet {A : Type u} [Poset (List A)] [DecidableEq A] (x y : List A) : List A :=
  match x,y with
  | [], [] => []
  | _, [] => []
  | [], _ => []
  | a::L, b::M => if a = b then a :: meet L M else []

theorem bot_le {A : Type u} [Poset (List A)] (x: List A) : [] <+: x := by
  exact nil_prefix

theorem meet_le {A : Type u} [Poset (List A)] [DecidableEq A] (x y : List A)
  : (meet x y) <+: x := by
  match x,y with
  | a::L, b::M =>
    simp[meet]
    split_ifs
    . have : IsPrefix (meet L M) L := by apply meet_le -- structural recursion!
      simp[this]
    . apply bot_le
  | [], [] => simp[meet]
  | a::L, [] => simp[meet]
  | [], b::M => simp[meet]

theorem meet_le' {A : Type u} [Poset (List A)] [DecidableEq A] (x y : List A)
  : (meet x y) <+: y := by
  match x,y with
  | a::L, b::M =>
    simp[meet]
    split_ifs
    . have : IsPrefix (meet L M) M := by apply meet_le' -- structural recursion!
      simp[this]
      assumption
    . apply bot_le
  | [], [] => simp[meet]
  | a::L, [] => simp[meet]
  | [], b::M => simp[meet]

theorem meet_great {A : Type u} [Poset (List A)] [DecidableEq A] (x y : List A)
  : ∀ w, w <+: x → w <+: y → w <+: (meet x y) := by
  intro w hwx hwy
  match x, y with
  | a::L, b::M =>
    simp[meet]
    split_ifs
    . rename_i hab
      simp_all[hab]
      by_cases hw : w = []
      . simp[hw]
      . obtain ⟨ c, ⟨ N, hcN ⟩ ⟩ := ne_nil_iff_exists_cons.mp hw
        simp_all[hcN]
        apply meet_great -- structural recursion!
        . exact hwx.right
        . exact hwy
    . rename_i hab
      have : w = [] := by
        by_cases h : w = []
        . exact h
        . have ⟨ c, ⟨ N, hN ⟩ ⟩ : ∃ c, ∃ N, w = c :: N := ne_nil_iff_exists_cons.mp h
          have h1 : c = a := by simp_all[hN]
          have h2 : c = b := by simp_all[hN]
          simp_all
      simp[this]
  | [], [] => simp[meet,hwx]
  | a::L, [] => simp[meet,hwy]
  | [], b::M => simp[meet,hwx]

instance info_semilattice {A : Type u} [DecidableEq A] : Semilattice (List A) :=
  ⟨
    meet,
    λ L M => by
      constructor
      . constructor
        . apply meet_le
        . apply meet_le'
      . apply meet_great
  ⟩
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
