--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib
import Lean

namespace LeanW26

--notdone

/-
Tactics
===

What's a Tactic?
===

Writing proofs at the term level becomes cumbersome for more advanced examples.

Tactics are a way to
- automate the construction of terms involving constructors and recursors
- break up proofs into sub-goals
- search for and apply applicable theorems and lemmas
- search for entire proofs
- make proofs look more like math and less like programming

Tactics are written in Lean itself using _meta-programming_, which we will
cover later in this course. For now, we will learn to use tactics to see
what they can do.

A tactic proof is used to build a term-level proof which is then checked
by the kernel. Thus, if there are mistakes in a tactic script, the kernel
will find them.


Tactic Documentation
===

There are more than  550 tactics defined in Lean's standard library and Mathlib.

-/

#help tactic -- lists all tactics

/-
<div style='font-size: 5pt; font-family: "courier"; margin-bottom: 10px' >
#adaptation_note, #check, #count_heartbeats, #count_heartbeats!, #find, #leansearch, #loogle, #loogle, #search, #statesearch, (, <;>, <;>, _, abel, abel!, abel1, abel1!, abel_nf, abel_nf!, absurd, ac_change, ac_nf, ac_nf0, ac_rfl, admit, aesop, aesop?, aesop_cat, aesop_cat?, aesop_cat_nonterminal, aesop_graph, aesop_graph?, aesop_graph_nonterminal, aesop_mat, aesop_unfold, aesop_unfold, algebraize, algebraize_only, all_goals, and_intros, any_goals, apply, apply, apply, apply?, apply_assumption, apply_ext_theorem, apply_fun, apply_gmonoid_gnpowRec_succ_tac, apply_gmonoid_gnpowRec_zero_tac, apply_mod_cast, apply_rewrite, apply_rfl, apply_rules, apply_rw, arith_mult, arith_mult?, array_get_dec, array_mem_dec, as_aux_lemma, assumption, assumption', assumption_mod_cast, attempt_all, aux_group₁, aux_group₂, bddDefault, beta_reduce, bicategory, bicategory_coherence, bicategory_coherence, bicategory_nf, bitwise_assoc_tac, borelize, bound, bv_check, bv_decide, bv_decide, bv_decide?, bv_decide?, bv_normalize, bv_normalize, bv_omega, by_cases, by_cases!, by_contra, by_contra!, calc, calc?, cancel_denoms, cancel_denoms, case, case, case', case', cases, cases', cases_first_enat, cases_type, cases_type!, casesm, casesm!, cat_disch, cc, cfc_cont_tac, cfc_tac, cfc_zero_tac, change, change, change?, check_compositions, choose, choose!, classical, clean, clean_wf, clear, clear, clear!, clear_, clear_aux_decl, clear_value, coherence, compareOfLessAndEq_rfl, compute_degree, compute_degree!, congr, congr, congr, congr!, congrm, congrm?, constructor, constructorm, continuity, continuity?, contradiction, contrapose, contrapose!, conv, conv', conv?, conv_lhs, conv_rhs, convert, convert_to, cutsat, dbg_trace, decide, decreasing_tactic, decreasing_trivial, decreasing_trivial_pre_omega, decreasing_with, delta, deriving_LawfulEq_tactic, deriving_LawfulEq_tactic_step, deriving_ReflEq_tactic, discrete_cases, done, dsimp, dsimp!, dsimp?, dsimp?!, eapply, econstructor, else, else, enat_to_nat, eq_refl, erw, erw?, eta_expand, eta_reduce, eta_struct, exact, exact?, exact_mod_cast, exacts, exfalso, exists, existsi, expose_names, ext, ext1, extract_goal, extract_lets, fail, fail_if_no_progress, fail_if_success, false_or_by_contra, fapply, fconstructor, field, field_simp, field_simp_discharge, filter_upwards, fin_cases, fin_omega, find, finiteness, finiteness?, finiteness_nonterminal, first, focus, forward, forward?, frac_tac, fun_cases, fun_induction, fun_prop, funext, gcongr, gcongr?, gcongr_discharger, generalize, generalize', generalize_proofs, get_elem_tactic, get_elem_tactic_extensible, get_elem_tactic_trivial, ghost_calc, ghost_fun_tac, ghost_simp, grewrite, grind, grind?, grobner, group, grw, guard_expr, guard_goal_nums, guard_hyp, guard_hyp_nums, guard_target, have, have, have', haveI, hint, induction, induction', infer_instance, infer_param, inhabit, init_ring, injection, injections, interval_cases, intro, intro, intro, intros, introv, isBoundedDefault, itauto, itauto!, iterate, left, let, let, let, let', letI, let_to_have, lia, lift, lift_lets, liftable_prefixes, linarith, linarith!, linarith?, linarith?!, linear_combination, linear_combination', linear_combination2, map_fun_tac, map_tacs, massumption, massumption, match, match, match_scalars, match_target, mcases, mcases, mclear, mclear, mconstructor, mconstructor, mdup, measurability, measurability!, measurability!?, measurability?, mem_tac, mem_tac_aux, mexact, mexact, mexfalso, mexfalso, mexists, mexists, mfld_set_tac, mframe, mframe, mhave, mhave, mintro, mintro, mleave, mleave, mleft, mleft, mod_cases, module, monicity, monicity!, mono, monoidal, monoidal_coherence, monoidal_coherence, monoidal_nf, monoidal_simps, move_add, move_mul, move_oper, mpure, mpure, mpure_intro, mpure_intro, mrefine, mrefine, mrename_i, mrename_i, mreplace, mreplace, mrevert, mrevert, mright, mright, mspec, mspec, mspec_no_bind, mspec_no_simp, mspecialize, mspecialize, mspecialize_pure, mspecialize_pure, mstart, mstart, mstop, mstop, mv_bisim, mvcgen, mvcgen, mvcgen?, mvcgen_trivial, mvcgen_trivial_extensible, native_decide, next, nlinarith, nlinarith!, nofun, nomatch, noncomm_ring, nontriviality, norm_cast, norm_cast0, norm_num, norm_num1, nth_grewrite, nth_grw, nth_rewrite, nth_rw, observe, observe?, observe?, obtain, omega, on_goal, open, order, order_core, peel, pgame_wf_tac, pi_lower_bound, pi_upper_bound, pick_goal, plausible, pnat_positivity, pnat_to_nat, polyrith, positivity, pull, pure_coherence, push, push_cast, push_neg, qify, rcases, rcongr, recover, reduce, reduce_mod_char, reduce_mod_char!, refine, refine', refine_lift, refine_lift', refold_let, rel, rename, rename', rename_bvar, rename_i, repeat, repeat', repeat1, repeat1', replace, replace, restrict_tac, restrict_tac?, revert, rewrite, rewrite!, rfl, rfl', rfl_cat, rify, right, ring, ring!, ring1, ring1!, ring1_nf, ring1_nf!, ring_nf, ring_nf!, rintro, rotate_left, rotate_right, rsuffices, run_tac, rw, rw!, rw?, rw??, rw_mod_cast, rw_search, rwa, saturate, saturate?, says, set, set!, set_option, show, show_term, simp, simp!, simp?, simp?!, simp_all, simp_all!, simp_all?, simp_all?!, simp_all_arith, simp_all_arith!, simp_arith, simp_arith!, simp_intro, simp_rw, simp_wf, simpa, simpa!, simpa?, simpa?!, sizeOf_list_dec, skip, sleep, sleep_heartbeats, slice_lhs, slice_rhs, smul_tac, solve, solve_by_elim, sorry, sorry_if_sorry, specialize, specialize_all, split, split_ands, split_ifs, squeeze_scope, stop, subsingleton, subst, subst_eqs, subst_hom_lift, subst_vars, substs, success_if_fail_with_msg, suffices, suffices, suggestions, swap, swap_var, symm, symm_saturate, tauto, tauto_set, tfae_finish, tfae_have, tfae_have, toFinite_tac, to_encard_tac, trace, trace, trace_state, trans, transitivity, triv, trivial, try, try?, try_suggestions, try_this, type_check, unfold, unfold?, unfold_projs, unhygienic, uniqueDiffWithinAt_Ici_Iic_univ, unit_interval, unreachable!, use, use!, use_discharger, use_finite_instance, valid, volume_tac, wait_for_unblock_async, whisker_simps, whnf, with_panel_widgets, with_reducible, with_reducible_and_instances, with_unfolding_all, witt_truncateFun_tac, wlog, wlog!, zify
</div>

-/

#help tactic apply -- tells you about a specific tactic

/-
Entering Tactic Mode
===

Tactic mode is entered in a proof using the keyword `by`
-/

variable (p : Type → Prop)

theorem my_thm1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  sorry

/-
Here, `sorry` is a tactic that closes the proof, but uses the `sorryAx` axiom.
Lean then underlines the example keyword to denote that you still have work to do.
-/

#help tactic sorry

#print axioms my_thm1   -- 'LeanW26.my_thm' depends on axioms: [sorryAx]

/-
intro
===

Introduction applies to implications and forall statements, introducing either a new
hypothesis or a new object. It takes the place of `fun h₁ h₂ ... => ...`

Note also that by using `.` and indentation, you can visually break up your
proof to it is more readable. -/

example : (¬ ∃ x, p x) → (∀ x, ¬ p x) := by
  intro hnep x
  sorry

/-
apply
===

The `apply` tactic applies a function, for-all statement, or another theorem.
It looks for arguments that match its type signature in the context and
automatically uses them if possible. -/

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro h x hp               --  ⊢ False
    apply h                    --  ⊢ ∃ x, p x
    apply Exists.intro x       --  ⊢ p x
    apply hp                   --  Goals accomplished!
  · intro hnpx h
    apply Exists.elim h
    intro x hp
    apply hnpx x
    apply hp

/- The dots (entered as `\.`) help deliniate the subcases, isolating them in the Infoview.

This tactic proof compiles to the term level proof
```lean
fun p ↦ {
  mp := fun h x hp ↦ h (Exists.intro x hp),
  mpr := fun h hepx ↦ Exists.elim hepx fun x hpa ↦ h x hpa
}
```


apply with Other Theorems
===

You can use `apply` and `exact` with perviously defined theorems.

-/

theorem my_thm2 (q : Prop) : q → q := id

example (q : ℕ → Prop) : (∀ x, q x) → ∀ x, q x := by
  apply my_thm2

#check Eq.symm  -- defined in Init.Prelude

example (x y : ℕ) : x = y → y = x := by
  apply Eq.symm

/- If you are stuck, there is `apply?` -/

example (x y : ℕ) : x = y → y = x := by
  apply?         -- Try this:
                 --   [apply] exact fun a ↦ id
                 -- (Eq.symm a)

/- If you click on `[apply]` VS Code inserts the suggested proof (which
in this case isn't particuarly concise, but it works).-/


/-
exact
===

`exact` is a variant of apply that requires you to fill in the arguments you are using.
It essentially pops you out of tactic mode. It is used at the end of proofs to make things
more clear and robust to changes in how other tactics in the proof are applied.

Here is the previous proof presented more compactly. -/

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro h x hp
    exact h (Exists.intro x hp)
  · intro h hepx
    apply Exists.elim hepx
    intro x hpa
    exact (h x) hpa

/- And even more compactly using structure notation and matching -/

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro h x hp
    exact h (Exists.intro x hp)
  · intro h ⟨ x, hp ⟩
    exact (h x) hp

/-
use
===
apply `Exists.intro x` is quite common. The tactic `use` wraps it
and allows for multiple introductions at the same time.
-/

example : ∀ (x : ℕ), ∃ y, x < y := by
  intro x
  use x+1
  apply?       -- Try this:
               --   [apply] exact lt_add_one x

example : ∀ (x : ℕ), ∃ y, x < y := by
  intro x
  use x+1
  exact lt_add_one x

example : ∃ (x:ℕ), ∃ y, x < y := by
  use 0, 1
  exact Nat.one_pos




/-
assumption
===

This tactic looks through the context to find an assumption that applies,
and applies it. It is like apply but where you don't even say what to apply. -/

example (c : Type) (h : p c) : ∃ x, p x := by
  apply Exists.intro c
  assumption

/-
Exercise
===
-/


/-
Packaging And and Exists
===

Recall that `And` and `Exists` are defined inductively. We can use brackets
to invoke their constructors as described in the _Datatypes_ slide deck in proofs as well. -/

example (p : Prop) : p → (p ∧ p) := by
  intro hp
  exact ⟨ hp, hp ⟩

example (p : Type → Prop) (c : Type) : (∀ x, p x) → ∃ x, p x :=
  fun h => ⟨ c, h c ⟩

/- Brackets work on any structure / inductive type : -/

structure Point where
  x : ℕ
  y : ℕ

example : ∃ (p : Point) , p.x = 0 :=  by
  exact ⟨ ⟨ 0, 0 ⟩, rfl ⟩




/-
Pattern Matching
===

You can match also constructors with `intro` to more easily break up expressions. -/

example (p q : Prop) : p ∧ q → q := by
  intro ⟨ _, hq ⟩
  exact hq

example : (∃ x , ¬p x) → ¬ ∀ x, p x := by
  intro ⟨ x, hnp ⟩ hnap
  exact hnp (hnap x)

example (P Q : Type → Prop): (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro ⟨ x, ⟨ hp, hq ⟩ ⟩
  exact ⟨ x, ⟨ hq, hp ⟩ ⟩



/-
FOL Examples Revisited
===

Now that we can use tactics, our First Order Logic Proofs can be made to look a little
cleaner, although one might argue the use of angled brackets is harder to read. -/

variable (p : Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  · intro ⟨ x, ⟨ hx, hr ⟩ ⟩
    exact ⟨ ⟨ x, hx ⟩ , hr ⟩
  · intro ⟨ ⟨ x, hx ⟩ , hr ⟩
    exact ⟨ x, ⟨ hx, hr ⟩ ⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  · intro h x hp
    exact h ⟨ x, hp ⟩
  · intro h ⟨ x, hp ⟩
    exact h x hp

/-
`have` and `let`
===

You can use `have` to record intermediate results -/

example (p q : Prop) : p ∧ q → p ∨ q := by
  intro ⟨ h1, h2 ⟩
  have hp : p := h1
  exact Or.inl hp

/- If you need an intermediate value, you should use `let`. -/

example : ∃ n , n > 0 := by
  let m := 1
  exact ⟨ m, Nat.one_pos ⟩

/-
cases
===

The `cases` tactic wraps around `Or.elim` to make proofs easier to read. For example, -/

example (p q : Prop) : (p ∨ q) → q ∨ p  := by
  intro h
  apply Or.elim h
  · intro hp
    exact Or.symm h
  · intro hq
    exact Or.symm h

/- Becomes -/

example (p q : Prop) : (p ∨ q) → q ∨ p  := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.symm (Or.inr hq)




/-
Cases Works With any Inductive Type
===

Here's are some alternative ways to prove some simple results -/

variable (P Q : Type → Prop)

example : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  cases h with
  | intro x h => exact ⟨ x, And.symm h ⟩

example (p q : Prop) : (p ∧ q) → (p ∨ q) :=  by
  intro h
  cases h with
  | intro hp hq => exact Or.inl hp

/-
Cases with Person
===
-/

--hide
inductive Person where | mary | steve | ed | jolin

open Person
--unhide

/- Recall that `on_right` was defined as -/

def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary

/- We can do a proof by cases with `Person` using the `cases` tactic -/

example : ∀ x : Person, ∃ y, ¬on_right x y := by
  intro hp
  cases hp with
  | mary =>                 -- ⊢ ∃ y, ¬on_right mary y
    use jolin               -- ⊢ ¬on_right mary jolin
    intro h                 -- on_right mary jolin ⊢ False
    cases h                 -- Subgoal accomplished
                            -- There are no cases in which on_right mary jolin is true
  | steve => sorry
  | ed => sorry
  | jolin => sorry



/-
`by_cases`
===

The `cases` tactic is not to be confused with the `by_cases` tactic,
may use resort to classical reasoning. -/

theorem cases_example (p : Prop) : p ∨ ¬p := by
  by_cases h : p
  · exact Or.inl h -- show p ∨ ¬p assuming h : p
  · exact Or.inr h -- show p ∨ ¬p assuming h : ¬p

#print axioms cases_example    --  [propext, Classical.choice, Quot.sound]

/- However, `by_cases` on a non-prop usually does not require classical reasoning. -/

theorem another_example : ∀ n : ℕ, n = 0 ∨ n > 0 := by
  intro n
  by_cases h : n = 0
  · exact Or.inl h
  · apply Or.inr
    exact Nat.zero_lt_of_ne_zero h     -- obtained via apply?

#print axioms another_example      -- does not depend on any axioms
                                   -- since it can be proved by induction

/-
Exercise
===
-/

/-
Induction
===

Consider the natural numbers and suppose `P : Nat → Prop` is a
property. To prove `P` with induction, you prove `P(0)` and `∀ n, P(n) → P(n+1)`. -/

def E (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ x => ¬E x

example : ∀ n : Nat, E n ∨ E n.succ := by
  intro n
  induction n with
  | zero => exact Or.inl True.intro
  | succ k ih =>
    apply Or.elim ih                           -- ih : E k ∨ E k.succ
    · intro h                                  -- h  : E k
      exact Or.inr (fun a => a h)              -- ⊢ E (k + 1) ∨ E (k + 1).succ
    · intro h
      exact Or.inl h

/-
Induction on any Inductive Type
===
-/

example {p q : Prop} : p ∧ q → q ∧ p := by
  intro hpq
  induction hpq with
  | intro left right => exact ⟨ right, left ⟩

example {p : ℕ → Prop} : (∃ x, ¬p x) → ¬∀ x, p x := by
  intro h1 h2
  induction h1 with
  | intro w h => exact h (h2 w)



/-
Exercise
===

<ex /> TODO: Proof by induction on PreDyadics.

<ex /> TODO: student looks up a tactic and uses it in a proof of an example defined here.

-/

/-
Defining New Tactics
===

You can define your own tactics. Here is an example. We will cover this
and other "meta-programming" methods later.

You will need to `import Lean`.

-/

open Lean Elab Tactic

syntax (name := myTacticSyntax) "my_tactic" : tactic

@[tactic myTacticSyntax]
def myTactic : Tactic := fun _ => do
  try
    evalTactic (← `(tactic| rfl))
  catch _ =>
    throwError "my_tactic: could not solve the goal"

example : 0 = 0 := by
  my_tactic             -- yay it works!


/-
It only works when rfl does though.
```lean
example (p : Prop) : p := by my_tactic      -- my_tactic: could not solve the goal
```
-/

--hide
end LeanW26
--unhide
