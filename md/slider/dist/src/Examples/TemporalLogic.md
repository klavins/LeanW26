
Temporal Logic
===


Example: A Microwave Oven Door
===


Consider a FSM that has three states.
```
   1.  closed  ⟶   2. ¬closed
       off     ⟵       off
        ↑ ↓
   3.  closed
      ¬off
```
Each state is labeled by a set of properties that are true in that state. Questions we might have about this model:

  - Starting in state 1, is it always true that if the oven is on, then the door is closed?
  - Is it always the case the if the oven is on, then it is eventually off?
  - Etc.

To approach these questions, we will:
  - Learn about `Set`
  - Define `Kripke Structures` = states + assignments of states ot properties
  - Define the notion of a `Trace` over states
  - Define the notion of a `Trajectory` over props
  - Develop a `Temporal Logic` that let's us state the above quetions
  - Develop a proof theory for checking temporal logic statements. 

Kripke Structures
===

```lean
structure Kripke where
  states : Type                      -- The type of states (e.g. numbers)
  next : states → Set states        -- Given a state, what's the next state?
  label : states → Set Prop         -- Given a state, what is true of the state?
```

Microwave State
===

```lean
inductive MWState where
  | one
  | two
  | three
  deriving Repr

open MWState
```

Properties of States
===

```lean
inductive closed : Prop where
  | a : closed

inductive off : Prop where

@[simp]
theorem closed_ne_off : closed ≠ off := by
  intro h
  nomatch h.mp closed.a

-- structure MWProp where
--    off : Prop
--    closed : Prop

-- open MWProp

-- #check ({off} : Set Prop)
```

Microwave Kripke
===

```lean
def MW : Kripke := {
  states := MWState,
  next  := fun s => match s with
    | one   => {two, three}
    | two   => {one}
    | three => {one},
  label := fun s => match s with
    | one   => {closed,off}
    | two   => {off}
    | three => {closed}
}
```

Traces
===

We can now start defining `Linear Temporal Logic` or `LTL`, which is a logic for reasoning about sequences of states, which the literature calls `Traces`. Eventually we will define operators like:

  now P                : P is true in the first state
  later P n            : P is true at step n
  eventually           : P is true at some point in the future
  always               : P is true always

Some of this is inspired by

  https://github.com/GaloisInc/lean-protocol-support/


```lean
universe u

def Trace (T : Type u) : Type u := Nat -> T

-- example: the microwave does nothing forever
def M : Trace MWState := fun _ => one
```

Sequence Properties
===

```lean
def tProp (T : Type u) := Set (Trace T)


-- Example: Sequences that are definitely one at step 10
def N10 : tProp MWState := λ τ => τ 10 = one

-- Example: Sequences that are one at some point
def EV1 : tProp MWState :=  λ τ => ∃ n, τ n = one

-- Example: Sequences that are always one
def AL1 : tProp MWState :=  λ τ => ∀ n, τ n = one

-- Example: Sequences that are never two
def NVT : tProp MWState :=  λ τ => ∀ n, τ n ≠ two

-- **Exercise** Define a sequence that is always three immediately
-- after it is two
def TAT : tProp MWState := λ τ => ∀ n, τ n = two → τ (n+1) = three
```

tProp is a Set
===

```lean
#check_failure EV1 ∩ AL1

instance {T: Type u} : Inter (tProp T) := ⟨ Set.inter ⟩    -- ∩
instance {T: Type u} : Union (tProp T) := ⟨ Set.union ⟩    -- ∪
instance {T: Type u} : HasSubset (tProp T) :=  ⟨λ S T => ∀ a, S a → T a⟩ -- ⊆
instance {T: Type u} : Membership (Trace T) (tProp T) := ⟨ id ⟩
instance {T: Type u} : EmptyCollection (tProp T) :=  ⟨ { _x | False } ⟩
instance {T: Type u} : HasCompl (tProp T) :=  ⟨ λ S => { x | ¬S x } ⟩

#check EV1 ∩ AL1
```

Combining Properties
===

The simplest way to combine sequence properties is with set operations. 
```lean
#check EV1 ∩ NVT  --- Evenually one and never two
#check EV1 ∪ NVT  --- Evenually one or never two

#check EV1 (λ _ => one)

-- If every state is a one, then eventually the state is one
example : AL1 ⊆ EV1 := by
  intro x h
  simp_all[AL1,EV1]

-- **Exercise** prove the following
example : N10 ⊆ EV1 := by
  intro x h
  simp_all[N10,EV1]
  use 10
```

The Shift Operator
===

Takes a Trace τ = ⟨ τ₀, τ₁, τ₂, τ₃, τ₄, τ₅, ... ⟩  and returns the `rest of the Trace` after a given point in time. E.g.

  shift τ 3 = ⟨ τ₃, τ₄, τ₅, ... ⟩


```lean
@[simp]
def shift {T: Type u} (τ : Trace T) (i : Nat) :=
  λ (n : Nat) => τ (n + i)
```

Theorems about Shift
===

```lean
theorem s_compose {T: Type} {τ : Trace T} {i j: ℕ}
  : shift (shift τ i) j = shift τ (i+j) := by
  apply funext
  intro n
  simp
  have : n + j + i = n + (i + j) := by linarith
  simp[this]

-- **Exercise** Prove this theorem about wrapping indices
theorem s_swap {T: Type} {τ : Trace T} {i j: ℕ}
  : shift (shift τ i) j = shift (shift τ j) i := by
  apply funext
  intro n
  simp
  have : n + j + i = n + i + j := by linarith
  simp[this]
```

Now and Later
===

```lean
@[simp]
def later {T : Type u} (P : Set T) (n: Nat) : tProp T :=
  λ τ => P (τ n)

@[simp]
def now {T : Type u} (P: T -> Prop) : tProp T := later P 0

@[simp]
def is (x : MWState) := λ y => y=x

#check later (is one) 3          -- the state is one at step 3
#check now (is two)              -- the current state is two

example (τ:Trace MWState)
  : τ ∈ AL1 → now (is one) τ := by
  intro h
  exact h 0

-- **Exercise** Prove the following
example (n:ℕ) (τ:Trace MWState)
  : AL1 τ → later (is one) n τ := by
  intro h
  exact h n
```

Next
===

```lean
-- P holds n steps in the future -/
@[simp]
def argnext {T : Type u} (n : Nat) (P : tProp T) : tProp T
  := λ τ => P (shift τ n)

-- P holds in the next step
@[simp]
def next {T : Type u} : tProp T → tProp T := argnext 1

-- example trajectory: 1 1 ... 1 2 2 2 ...
def τ12 : Trace MWState :=
  λ n => if n < 10 then one else two

example : argnext 10 (now (is two)) τ12 := by rfl

example : next (later (is two) 9) τ12 := by rfl

-- **Exericse** Show the following
example {n:ℕ} : argnext (n+1) (now P) = next (later P n) := by
  funext τ
  simp
```

Always
===

```lean
@[simp]
def always {T: Type u} (P : tProp T) : tProp T :=
  λ (τ : Trace T) => ∀ n , P (shift τ n)

example : ¬always (now (is one)) τ12 := by
  intro h1
  simp[τ12] at h1
  have h2 : 10 < 10 := h1 10
  apply (lt_self_iff_false 10).mp h2

-- **Exercise** Prove the following:
example {τ:Trace MWState}:
  always (now (is three)) τ → ¬(now (is two)) τ := by
  intro h1 h2
  --have h3 := h1 0
  simp_all
```

EVENTUALLY
===

```lean
@[simp]
def eventually {T: Type u} (P : tProp T) : tProp T :=
  λ (τ : Trace T) => ∃ n, P (shift τ n)

example : eventually (now (is two)) τ12 := by
  use 10
  simp[eventually,now,later,shift,is,one,τ12]

def τ1212 : Trace MWState := λ n => if n%2 = 0 then two else one

example : always (eventually (later (is two) 1)) τ1212 := by
  intro k
  simp[is,τ1212]
  use k+1
  have : 1 + (k + 1) + k = 2*(k+1) := by linarith
  simp[this]
```

Another Eventually Example
===

```lean
-- **Exercise** Hint: Use Set.subset_setOf.mpr and Set.mem_def
theorem subset_event {T: Type u} {P Q: tProp T}
  : P ⊆ Q → eventually P ⊆ eventually Q := by
  intro hpq τ ⟨ n, h ⟩
  use n
  exact hpq (shift τ n) h
```

Implication
===

```lean
def implies {T : Type u} (P Q : Set T) : Set T :=
  λ x => P x → Q x
```

Tautologies
===

```lean
def satisfies {T : Type u} (τ : Trace T) (p : tProp T) := p τ

def tautology {T : Type u} (p : tProp T) := ∀ τ , p τ

-- same statement as previous example, but no ⊆
theorem eventually_monotonic {T: Type u} {P Q: tProp T}
  : P ⊆ Q → tautology (implies (eventually P) (eventually Q)) :=
  sorry

-- **Exercise** Prove the following theorem
theorem always_eventually {T : Type u} (A : tProp T)
  : tautology (implies (always A) (eventually A)) :=  by
  intro τ h
  use 0
  exact h 0
```
 Many more theorems can be stated and proved 

Verifying Properties of Kripke Structures
===

So far we have not used the `next` and `label` relations in the Kripke Structure.

   1.  closed  ⟶   2. ¬closed
       off     ⟵       off
        ↑ ↓
   3.  closed
      ¬off

structure Kripke where
  states: Type
  next : states → Set states
  label : states → Set Prop

We need a notion of a `trajectory` over propositions that respects the transition function.



Trajectories
===

A `Trajectory` is a Trace over sets of propositions, listing what is true at each time point.

A trajectory σ `Respects` a Kripke structure if:

  1) There is some trace τ over states such that
  2) For every time point n
  3) τ respects M.next and σ respects M.label


```lean
def Trajectory := Trace (Set Prop)

-- Example trajectory. Does not actually respect MW
def idle : Trajectory := λ _ => {off}
```

Trajectory Properties
===

```lean
def kProp := tProp (Set Prop)

instance : HasSubset kProp  := ⟨ Set.Subset ⟩
instance : Union kProp := ⟨ Set.union ⟩
instance : Membership Trajectory kProp where mem P σ := P σ
instance : Inter kProp := ⟨ Set.inter ⟩

-- Example: Always Off
def AO : kProp := λ σ => ∀ n, σ n off
```

Satisfaction
===

Here we define what it means for an individual trajectory to respect the transition and labeling function of a Kripke structure.

And we define satisifaction to mean that all trajectories in a kProp respect a Kripke Structure. 
```lean
@[simp]
def respects (M : Kripke) (σ : Trajectory) : Prop :=
  ∃ (τ : Trace M.states),
  ∀ (n : Nat),
  τ (n+1) ∈ M.next (τ n) ∧ σ n = M.label (τ n)

@[simp]
def k_satisfies (M : Kripke) (φ : kProp) :=
  ∀ (σ : Trajectory) , respects M σ → φ σ
```

You Never Have to Turn on the Microware
===

```lean
-- **Exercise** Complete the following proof
example : k_satisfies MW AO := by
  simp
  intro σ τ h
  intro n
  have ⟨ htraj, hlabel ⟩ := h n
  have ⟨ htraj', hlabel' ⟩ := h (n+1)

  cases hs : τ n

  -- one
  . simp[hs] at hlabel
    simp[hlabel,MW]
    apply Set.mem_def.mp
    apply Set.mem_insert_iff.mpr
    apply Or.inr rfl

  -- two
  . simp[hs] at hlabel
    simp[hlabel,MW]
    exact rfl

  -- three
  . simp_all[hs,MW,hs,htraj]
    -- AAHHH! THIS ISN'T ACTUALLY TRUE!
    sorry


-- Here's a quick and ditry proof that the opposite of the above is true.
-- It could be cleaned up a lot!
example : ¬k_satisfies MW AO := by
  simp
  let σ : Trajectory := (λ n => if n%2 = 0 then {closed,off} else {closed})
  let τ : Trace MWState := (λ n => if n%2 = 0 then one else three)
  use σ
  apply And.intro
  . use τ
    intro n
    by_cases h1 : n % 2 = 0
    . have h2 : τ n = one := if_pos h1
      have h3 : (n+1) % 2 = 1 := Nat.succ_mod_two_eq_one_iff.mpr h1
      have h4 : (n+1) % 2 ≠ 0 := by exact Nat.mod_two_ne_zero.mpr h3
      have h5 : τ (n+1) = three := by exact if_neg h4
      apply And.intro
      . simp[h5,MW,h2]
      . simp[h5,MW,h2]
        have h6 : σ n = {closed,off} := by exact if_pos h1
        simp[h6]
    . have h6 : τ n = three := if_neg h1
      have h7 : n%2 = 1 := Nat.mod_two_ne_zero.mp h1
      have h8 : (n+1)%2 = 0 := Nat.succ_mod_two_eq_zero_iff.mpr h7
      have h9 : τ (n+1) = one := by exact if_pos h8
      apply And.intro
      . simp[h9,h6,MW]
      . simp[h9,MW,h6]
        have h10 : σ n = {closed} := by exact if_neg h1
        simp[h10]
  . intro h
    simp_all[AO]
    have h' := h 1
    simp at h'
    have : σ 1 = {closed} := by exact rfl
    simp[this] at h'
    apply Set.mem_def.mpr at h'
    simp[Set.mem_insert_iff] at h'
    have h10 := closed_ne_off
    simp at h10
    exact h10 (id (Iff.symm h'))
```

Atomic
===

In logic and atopic proposition is one that cannot be broken down further. In temporal logic, that is taken to mean a proposition that is true at the initial state of a trajectory. 
```lean
def atomic (p : Prop) : kProp :=
  λ (σ : Trajectory ) => p ∈ (σ 0)

def AO' : kProp := always (atomic off)
def EO  : kProp := eventually (atomic off)
def AEO : kProp := always (eventually (atomic off))
```

Example Theorem
===

```lean
lemma always_union {M:Kripke} {p q: Prop}
  : ( ∀ state , p ∈ M.label state ∨ q ∈ M.label state )
  → k_satisfies M (always (atomic p ∪ atomic q)) := by

    intro h σ is_traj n
    apply Exists.elim is_traj
    intro τ traj_details
    have ⟨ _, in_label ⟩ := traj_details n
    have h1 := h (τ n)
    cases h1 with
    | inl h2 => (exact Or.inl (by
      apply Set.mem_setOf.mpr
      simp[in_label]
      exact h2
    ))
    | inr h3 => (exact Or.inr (by
      apply Set.mem_setOf.mpr
      simp[in_label]
      exact h3
    ))




notation:65 lhs:65 " ⊨ " rhs:66 => k_satisfies lhs rhs
```

Theorem Application
===

```lean
example : MW ⊨ (always (atomic off ∪ atomic closed)) := by
  exact always_union (by
    intro x
    cases x
    . exact Or.inl (Set.mem_insert_of_mem closed rfl)
    . exact Or.inl rfl
    . exact Or.inr rfl
  )
```

Other Examples
===

```lean
example : MW ⊨ (always (eventually (atomic off))) := by
  intro σ h k
  unfold eventually
  obtain ⟨ τ, h1 ⟩ := h
  cases hs : τ k
  . use 0
    simp[atomic]
    have ⟨ h2, h3 ⟩ := h1 k
    simp[h3,MW,hs]
  . use 0
    simp[atomic]
    have ⟨ h2, h3 ⟩ := h1 k
    simp[h3,MW,hs]
  . use 1
    simp[atomic,MW]
    have ⟨ h2, h3 ⟩ := h1 k
    simp_all[hs]
    have h5 : τ (k+1) = one := by exact h2
    have h6 : k+1 = 1+k := by exact Nat.add_comm k 1
    simp[h6] at h5
    simp[h5]
    apply Set.mem_insert_iff.mpr
    exact Or.inr rfl



example : MW ⊨ (always (eventually (atomic (¬off)))) := by
  sorry
```

Tautologies Again
===

```lean
def k_tautology (p : kProp) := ∀ M : Kripke, k_satisfies M p

theorem atomic_inter {p q: Prop}
  : k_tautology (implies (atomic p ∩ atomic q) (atomic p)) := by
  intro h1
  simp
  intro τ M h2 h3
  apply Set.mem_def.mpr at h3
  simp[Set.mem_inter_iff] at h3
  exact h3.left

-- **Exercise** Prove the following
theorem atomic_union {p q: Prop}
  : k_tautology (implies (atomic p) (atomic p ∪ atomic q)) :=
  sorry
```

Conclusion
===

Kripke structures and Linear Temporal Logic (LTL) are the basis of the field of `Model Checking`, which has been applied to verificiation of programs, embedded systems, robotics, spacecraft and much more.

There are many theorems that can be proved regarding tautologies that can be used instead of the simplifier to make proving properties about models easier.

LTL can be extended to CTL = Computation Tree Logic, which includes branching (as in "at least one of the future paths satisifes a property"). There are also real time and probabilisitic versions.

Avanced model checking algorithms do not use theorem proving (yet). Instead they rely on explicitly enumerating states and trajectories, using clever pruning strategies to hand systems with `millions` of states.

For example: https://spinroot.com/spin/whatispin.html 
```lean
--hide
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

