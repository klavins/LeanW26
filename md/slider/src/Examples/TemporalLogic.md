
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


<div class="lean-code" data-start-line="69" data-end-line="72"><pre><code>structure Kripke where
  states : Type                      -- The type of states (e.g. numbers)
  next : states → Set states        -- Given a state, what&#x27;s the next state?
  label : states → Set Prop         -- Given a state, what is true of the state?</code></pre></div>


Microwave State
===


<div class="lean-code" data-start-line="79" data-end-line="85"><pre><code>inductive MWState where
  | one
  | two
  | three
  deriving Repr

open MWState</code></pre></div>


Properties of States
===


<div class="lean-code" data-start-line="93" data-end-line="109"><pre><code>inductive closed : Prop where
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

-- #check ({off} : Set Prop)</code></pre></div>


Microwave Kripke
===


<div class="lean-code" data-start-line="116" data-end-line="126"><pre><code>def MW : Kripke := {
  states := MWState,
  next  := fun s =&gt; match s with
    | one   =&gt; {two, three}
    | two   =&gt; {one}
    | three =&gt; {one},
  label := fun s =&gt; match s with
    | one   =&gt; {closed,off}
    | two   =&gt; {off}
    | three =&gt; {closed}
}</code></pre></div>


Traces
===

We can now start defining `Linear Temporal Logic` or `LTL`, which is a logic for reasoning about sequences of states, which the literature calls `Traces`. Eventually we will define operators like:

  now P                : P is true in the first state
  later P n            : P is true at step n
  eventually           : P is true at some point in the future
  always               : P is true always

Some of this is inspired by

  https://github.com/GaloisInc/lean-protocol-support/



<div class="lean-code" data-start-line="149" data-end-line="154"><pre><code>universe u

def Trace (T : Type u) : Type u := Nat -&gt; T

-- example: the microwave does nothing forever
def M : Trace MWState := fun _ =&gt; one</code></pre></div>


Sequence Properties
===


<div class="lean-code" data-start-line="173" data-end-line="190"><pre><code>def tProp (T : Type u) := Set (Trace T)


-- Example: Sequences that are definitely one at step 10
def N10 : tProp MWState := λ τ =&gt; τ 10 = one

-- Example: Sequences that are one at some point
def EV1 : tProp MWState :=  λ τ =&gt; ∃ n, τ n = one

-- Example: Sequences that are always one
def AL1 : tProp MWState :=  λ τ =&gt; ∀ n, τ n = one

-- Example: Sequences that are never two
def NVT : tProp MWState :=  λ τ =&gt; ∀ n, τ n ≠ two

-- **Exercise** Define a sequence that is always three immediately
-- after it is two
def TAT : tProp MWState := λ τ =&gt; ∀ n, τ n = two → τ (n+1) = three</code></pre></div>


tProp is a Set
===


<div class="lean-code" data-start-line="210" data-end-line="219"><pre><code>#check_failure EV1 ∩ AL1

instance {T: Type u} : Inter (tProp T) := ⟨ Set.inter ⟩    -- ∩
instance {T: Type u} : Union (tProp T) := ⟨ Set.union ⟩    -- ∪
instance {T: Type u} : HasSubset (tProp T) :=  ⟨λ S T =&gt; ∀ a, S a → T a⟩ -- ⊆
instance {T: Type u} : Membership (Trace T) (tProp T) := ⟨ id ⟩
instance {T: Type u} : EmptyCollection (tProp T) :=  ⟨ { _x | False } ⟩
instance {T: Type u} : HasCompl (tProp T) :=  ⟨ λ S =&gt; { x | ¬S x } ⟩

#check EV1 ∩ AL1</code></pre></div>


Combining Properties
===

The simplest way to combine sequence properties is with set operations. 

<div class="lean-code" data-start-line="239" data-end-line="253"><pre><code>#check EV1 ∩ NVT  --- Evenually one and never two
#check EV1 ∪ NVT  --- Evenually one or never two

#check EV1 (λ _ =&gt; one)

-- If every state is a one, then eventually the state is one
example : AL1 ⊆ EV1 := by
  intro x h
  simp_all[AL1,EV1]

-- **Exercise** prove the following
example : N10 ⊆ EV1 := by
  intro x h
  simp_all[N10,EV1]
  use 10</code></pre></div>


The Shift Operator
===

Takes a Trace τ = ⟨ τ₀, τ₁, τ₂, τ₃, τ₄, τ₅, ... ⟩  and returns the `rest of the Trace` after a given point in time. E.g.

  shift τ 3 = ⟨ τ₃, τ₄, τ₅, ... ⟩



<div class="lean-code" data-start-line="290" data-end-line="292"><pre><code>@[simp]
def shift {T: Type u} (τ : Trace T) (i : Nat) :=
  λ (n : Nat) =&gt; τ (n + i)</code></pre></div>


Theorems about Shift
===


<div class="lean-code" data-start-line="313" data-end-line="328"><pre><code>theorem s_compose {T: Type} {τ : Trace T} {i j: ℕ}
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
  simp[this]</code></pre></div>


Now and Later
===


<div class="lean-code" data-start-line="349" data-end-line="371"><pre><code>@[simp]
def later {T : Type u} (P : Set T) (n: Nat) : tProp T :=
  λ τ =&gt; P (τ n)

@[simp]
def now {T : Type u} (P: T -&gt; Prop) : tProp T := later P 0

@[simp]
def is (x : MWState) := λ y =&gt; y=x

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
  exact h n</code></pre></div>


Next
===


<div class="lean-code" data-start-line="383" data-end-line="403"><pre><code>-- P holds n steps in the future -/
@[simp]
def argnext {T : Type u} (n : Nat) (P : tProp T) : tProp T
  := λ τ =&gt; P (shift τ n)

-- P holds in the next step
@[simp]
def next {T : Type u} : tProp T → tProp T := argnext 1

-- example trajectory: 1 1 ... 1 2 2 2 ...
def τ12 : Trace MWState :=
  λ n =&gt; if n &lt; 10 then one else two

example : argnext 10 (now (is two)) τ12 := by rfl

example : next (later (is two) 9) τ12 := by rfl

-- **Exericse** Show the following
example {n:ℕ} : argnext (n+1) (now P) = next (later P n) := by
  funext τ
  simp</code></pre></div>


Always
===


<div class="lean-code" data-start-line="421" data-end-line="436"><pre><code>@[simp]
def always {T: Type u} (P : tProp T) : tProp T :=
  λ (τ : Trace T) =&gt; ∀ n , P (shift τ n)

example : ¬always (now (is one)) τ12 := by
  intro h1
  simp[τ12] at h1
  have h2 : 10 &lt; 10 := h1 10
  apply (lt_self_iff_false 10).mp h2

-- **Exercise** Prove the following:
example {τ:Trace MWState}:
  always (now (is three)) τ → ¬(now (is two)) τ := by
  intro h1 h2
  --have h3 := h1 0
  simp_all</code></pre></div>


EVENTUALLY
===


<div class="lean-code" data-start-line="462" data-end-line="477"><pre><code>@[simp]
def eventually {T: Type u} (P : tProp T) : tProp T :=
  λ (τ : Trace T) =&gt; ∃ n, P (shift τ n)

example : eventually (now (is two)) τ12 := by
  use 10
  simp[eventually,now,later,shift,is,one,τ12]

def τ1212 : Trace MWState := λ n =&gt; if n%2 = 0 then two else one

example : always (eventually (later (is two) 1)) τ1212 := by
  intro k
  simp[is,τ1212]
  use k+1
  have : 1 + (k + 1) + k = 2*(k+1) := by linarith
  simp[this]</code></pre></div>


Another Eventually Example
===


<div class="lean-code" data-start-line="489" data-end-line="494"><pre><code>-- **Exercise** Hint: Use Set.subset_setOf.mpr and Set.mem_def
theorem subset_event {T: Type u} {P Q: tProp T}
  : P ⊆ Q → eventually P ⊆ eventually Q := by
  intro hpq τ ⟨ n, h ⟩
  use n
  exact hpq (shift τ n) h</code></pre></div>


Implication
===


<div class="lean-code" data-start-line="511" data-end-line="512"><pre><code>def implies {T : Type u} (P Q : Set T) : Set T :=
  λ x =&gt; P x → Q x</code></pre></div>


Tautologies
===


<div class="lean-code" data-start-line="536" data-end-line="550"><pre><code>def satisfies {T : Type u} (τ : Trace T) (p : tProp T) := p τ

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
  exact h 0</code></pre></div>

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



<div class="lean-code" data-start-line="611" data-end-line="614"><pre><code>def Trajectory := Trace (Set Prop)

-- Example trajectory. Does not actually respect MW
def idle : Trajectory := λ _ =&gt; {off}</code></pre></div>


Trajectory Properties
===


<div class="lean-code" data-start-line="634" data-end-line="642"><pre><code>def kProp := tProp (Set Prop)

instance : HasSubset kProp  := ⟨ Set.Subset ⟩
instance : Union kProp := ⟨ Set.union ⟩
instance : Membership Trajectory kProp where mem P σ := P σ
instance : Inter kProp := ⟨ Set.inter ⟩

-- Example: Always Off
def AO : kProp := λ σ =&gt; ∀ n, σ n off</code></pre></div>


Satisfaction
===

Here we define what it means for an individual trajectory to respect the transition and labeling function of a Kripke structure.

And we define satisifaction to mean that all trajectories in a kProp respect a Kripke Structure. 

<div class="lean-code" data-start-line="666" data-end-line="674"><pre><code>@[simp]
def respects (M : Kripke) (σ : Trajectory) : Prop :=
  ∃ (τ : Trace M.states),
  ∀ (n : Nat),
  τ (n+1) ∈ M.next (τ n) ∧ σ n = M.label (τ n)

@[simp]
def k_satisfies (M : Kripke) (φ : kProp) :=
  ∀ (σ : Trajectory) , respects M σ → φ σ</code></pre></div>


You Never Have to Turn on the Microware
===


<div class="lean-code" data-start-line="689" data-end-line="756"><pre><code>-- **Exercise** Complete the following proof
example : k_satisfies MW AO := by
  simp
  intro σ τ h
  intro n
  have ⟨ htraj, hlabel ⟩ := h n
  have ⟨ htraj&#x27;, hlabel&#x27; ⟩ := h (n+1)

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
    -- AAHHH! THIS ISN&#x27;T ACTUALLY TRUE!
    sorry


-- Here&#x27;s a quick and ditry proof that the opposite of the above is true.
-- It could be cleaned up a lot!
example : ¬k_satisfies MW AO := by
  simp
  let σ : Trajectory := (λ n =&gt; if n%2 = 0 then {closed,off} else {closed})
  let τ : Trace MWState := (λ n =&gt; if n%2 = 0 then one else three)
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
    have h&#x27; := h 1
    simp at h&#x27;
    have : σ 1 = {closed} := by exact rfl
    simp[this] at h&#x27;
    apply Set.mem_def.mpr at h&#x27;
    simp[Set.mem_insert_iff] at h&#x27;
    have h10 := closed_ne_off
    simp at h10
    exact h10 (id (Iff.symm h&#x27;))</code></pre></div>


Atomic
===

In logic and atopic proposition is one that cannot be broken down further. In temporal logic, that is taken to mean a proposition that is true at the initial state of a trajectory. 

<div class="lean-code" data-start-line="771" data-end-line="776"><pre><code>def atomic (p : Prop) : kProp :=
  λ (σ : Trajectory ) =&gt; p ∈ (σ 0)

def AO&#x27; : kProp := always (atomic off)
def EO  : kProp := eventually (atomic off)
def AEO : kProp := always (eventually (atomic off))</code></pre></div>


Example Theorem
===


<div class="lean-code" data-start-line="798" data-end-line="822"><pre><code>lemma always_union {M:Kripke} {p q: Prop}
  : ( ∀ state , p ∈ M.label state ∨ q ∈ M.label state )
  → k_satisfies M (always (atomic p ∪ atomic q)) := by

    intro h σ is_traj n
    apply Exists.elim is_traj
    intro τ traj_details
    have ⟨ _, in_label ⟩ := traj_details n
    have h1 := h (τ n)
    cases h1 with
    | inl h2 =&gt; (exact Or.inl (by
      apply Set.mem_setOf.mpr
      simp[in_label]
      exact h2
    ))
    | inr h3 =&gt; (exact Or.inr (by
      apply Set.mem_setOf.mpr
      simp[in_label]
      exact h3
    ))




notation:65 lhs:65 &quot; ⊨ &quot; rhs:66 =&gt; k_satisfies lhs rhs</code></pre></div>


Theorem Application
===


<div class="lean-code" data-start-line="830" data-end-line="837"><pre><code>example : MW ⊨ (always (atomic off ∪ atomic closed)) := by
  exact always_union (by
    intro x
    cases x
    . exact Or.inl (Set.mem_insert_of_mem closed rfl)
    . exact Or.inl rfl
    . exact Or.inr rfl
  )</code></pre></div>


Other Examples
===


<div class="lean-code" data-start-line="852" data-end-line="879"><pre><code>example : MW ⊨ (always (eventually (atomic off))) := by
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
  sorry</code></pre></div>


Tautologies Again
===


<div class="lean-code" data-start-line="901" data-end-line="915"><pre><code>def k_tautology (p : kProp) := ∀ M : Kripke, k_satisfies M p

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
  sorry</code></pre></div>


Conclusion
===

Kripke structures and Linear Temporal Logic (LTL) are the basis of the field of `Model Checking`, which has been applied to verificiation of programs, embedded systems, robotics, spacecraft and much more.

There are many theorems that can be proved regarding tautologies that can be used instead of the simplifier to make proving properties about models easier.

LTL can be extended to CTL = Computation Tree Logic, which includes branching (as in "at least one of the future paths satisifes a property"). There are also real time and probabilisitic versions.

Avanced model checking algorithms do not use theorem proving (yet). Instead they rely on explicitly enumerating states and trajectories, using clever pruning strategies to hand systems with `millions` of states.

For example: https://spinroot.com/spin/whatispin.html 

<div class="lean-code" data-start-line="940" data-end-line="942"><pre><code>--hide
end LeanW26
--unhide</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

