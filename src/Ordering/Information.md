
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Ordering/Information.lean'>Code</a> for this chapter</span>
 # Information Ordering on Values 
```lean
def PartialFunction (A : Type u) (B : Type v) := A → Option B

namespace PartialFunction

def val_le (B : Type u) (u v : Option B) := u = none ∨ u = v

theorem val_le_refl {B : Type u} : Refl (val_le B) := by
  simp[Refl,val_le]

theorem val_le_anti_sym {B : Type u} : AntiSym (val_le B) := by
  intro x y h1 h2
  simp_all[val_le]
  aesop

theorem val_le_trans {B : Type u} : Trans (val_le B) := by
  intro x y z h1 h2
  simp_all[val_le]
  aesop

@[simp]
instance poset_val_le {B : Type u} : Poset (Option B) :=
  ⟨ val_le B, val_le_refl, val_le_anti_sym, val_le_trans ⟩

theorem none_val_le {B : Type u} : ∀ x : Option B, none ≤ x := by
  intro x
  have : val_le B none x := by simp[val_le]
  simp[Poset.le_inst,val_le]

def Dom {A : Type u} {B : Type v} (f: PartialFunction A B) : Set A := λ a => f a ≠ none

def le {A : Type u} {B : Type v} : Relation (PartialFunction A B) (PartialFunction A B) :=
  λ f g => ∀ x, (f x) ≤ (g x)


def bot {A : Type u} {B : Type v} : PartialFunction A B := λ _ => none

theorem le_refl {A : Type u} {B : Type v} : Refl (@le A B) := by
  intro x h
  apply val_le_refl

theorem le_anti_sym {A : Type u} {B : Type v} : AntiSym (@le A B) := by
  simp[AntiSym]
  intro f g hf hg
  funext x
  apply val_le_anti_sym
  . exact hf x
  . exact hg x

theorem le_trans {A : Type u} {B : Type v} : Trans (@le A B) := by
  simp[Trans]
  intro f g h hf hg
  simp[le]
  intro x
  apply val_le_trans
  . exact hf x
  . exact hg x

instance poset_le (A : Type u) (B : Type v): Poset (PartialFunction A B) :=
  ⟨ le, le_refl, le_anti_sym, le_trans ⟩

theorem le_def {A : Type u} {B : Type v} (f g: PartialFunction A B)
  : f ≤ g ↔ ∀ x, f x ≤ g x := by
  simp[le_inst, Poset.le, le, val_le]

theorem le_total_def {A : Type u} {B : Type v} (f g: PartialFunction A B)
  : f ≤ g ↔ ∀ x, f x = none ∨ f x = g x := by
  simp[le_inst, Poset.le, le, val_le]

theorem bot_le_all {A : Type u} {B : Type v} (f: PartialFunction A B) : bot ≤ f := by
  intro x
  simp[val_le,bot,Poset.le_inst]

theorem le_dom {A : Type u} {B : Type v} {f g : PartialFunction A B} :
  f ≤ g ↔ (Dom f ⊆ Dom g ∧ ∀ x ∈ Dom f, f x = g x):= by
  constructor
  . intro h
    constructor
    . intro a ha
      have := h a
      simp_all[Set.mem_def,Dom,val_le,Poset.le_inst]
    . intro a ha
      have := h a
      simp_all[Set.mem_def,Dom,Poset.le,val_le,le,Poset.le_inst]
  . intro ⟨ h1, h2 ⟩
    intro a
    have := h2 a
    simp_all[Set.mem_def,Dom,Poset.le,val_le,le]
    by_cases h3 : f a = none
    . exact Or.inl h3
    . apply Or.inr
      exact this h3

example (A : Type u) (B : Type v) (f : PartialFunction A B) : f ≤ f := by apply Poset.refl
```
 # Total Information Elements 
```lean
def Total {A : Type u} {B : Type v} (f : PartialFunction A B) := ∀ x, f x ≠ none

theorem total_le {A : Type u} {B : Type v} {f g : PartialFunction A B}
  : Total f → Poset.le f g → f = g := by
  simp[Total,Poset.le]
  intro h hfg
  funext x
  have h1 := h x
  have h2 := hfg x
  simp_all[val_le,Poset.le,Poset.le_inst]
```
 ## Information Ordering is a Lattice 
```lean
def meet {A : Type u} {B : Type v} [DecidableEq B] (f g : PartialFunction A B) :=
  λ a => if f a = g a then f a else none

theorem meet_symm {A : Type u} {B : Type v} [DecidableEq B] {f g : PartialFunction A B}
  : meet f g = meet g f := by
  unfold meet
  aesop

theorem pf_meet_le {A : Type u} {B : Type v} [DecidableEq B] {f g : PartialFunction A B} :
  (meet f g) ≤ f := by
  intro a
  simp[meet]
  split_ifs <;>
  simp[val_le,Poset.le_inst]

theorem pf_meet_le' {A : Type u} {B : Type v} [DecidableEq B] {f g : PartialFunction A B} :
  le (meet f g) g := by
  rw[meet_symm]
  exact pf_meet_le

theorem pf_meet_greater {A : Type u} {B : Type v} [DecidableEq B] {f g : PartialFunction A B} :
  ∀ w, le w f → le w g → le w (meet f g) := by
  intro w h1 h2 a
  simp[meet,val_le]
  split_ifs
  . exact h1 a
  . simp[Poset.le_inst,Poset.le,val_le,Poset.le_inst]
    apply Or.elim (h2 a)
    . exact id
    . intro h3
      cases h1 a with
      | inl h => simp_all
      | inr h => simp_all

instance info_semilattice {A : Type u} {B : Type v} [DecidableEq B] : Semilattice (PartialFunction A B) :=
  ⟨
    meet,
    λ _ _ => ⟨ ⟨ pf_meet_le, pf_meet_le' ⟩, pf_meet_greater ⟩
  ⟩

end PartialFunction
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
