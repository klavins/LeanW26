
Tactics
===
Most of the development in softare development has been in making programs easier to write, easier to understand, and easier to maintain.
Donald Knuth, <a href="https://www.cs.tufts.edu/~nr/cs257/archive/don-knuth/empirical-fortran.pdf">An Emperical Study of FORTRAN Progams</a>, 1971.


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


```lean
#help tactic -- lists all tactics
```

<div style='font-size: 5pt; font-family: "courier"; margin-bottom: 10px' >
#adaptation_note, #check, #count_heartbeats, #count_heartbeats!, #find, #leansearch, #loogle, #loogle, #search, #statesearch, (, <;>, <;>, _, abel, abel!, abel1, abel1!, abel_nf, abel_nf!, absurd, ac_change, ac_nf, ac_nf0, ac_rfl, admit, aesop, aesop?, aesop_cat, aesop_cat?, aesop_cat_nonterminal, aesop_graph, aesop_graph?, aesop_graph_nonterminal, aesop_mat, aesop_unfold, aesop_unfold, algebraize, algebraize_only, all_goals, and_intros, any_goals, apply, apply, apply, apply?, apply_assumption, apply_ext_theorem, apply_fun, apply_gmonoid_gnpowRec_succ_tac, apply_gmonoid_gnpowRec_zero_tac, apply_mod_cast, apply_rewrite, apply_rfl, apply_rules, apply_rw, arith_mult, arith_mult?, array_get_dec, array_mem_dec, as_aux_lemma, assumption, assumption', assumption_mod_cast, attempt_all, aux_group₁, aux_group₂, bddDefault, beta_reduce, bicategory, bicategory_coherence, bicategory_coherence, bicategory_nf, bitwise_assoc_tac, borelize, bound, bv_check, bv_decide, bv_decide, bv_decide?, bv_decide?, bv_normalize, bv_normalize, bv_omega, by_cases, by_cases!, by_contra, by_contra!, calc, calc?, cancel_denoms, cancel_denoms, case, case, case', case', cases, cases', cases_first_enat, cases_type, cases_type!, casesm, casesm!, cat_disch, cc, cfc_cont_tac, cfc_tac, cfc_zero_tac, change, change, change?, check_compositions, choose, choose!, classical, clean, clean_wf, clear, clear, clear!, clear_, clear_aux_decl, clear_value, coherence, compareOfLessAndEq_rfl, compute_degree, compute_degree!, congr, congr, congr, congr!, congrm, congrm?, constructor, constructorm, continuity, continuity?, contradiction, contrapose, contrapose!, conv, conv', conv?, conv_lhs, conv_rhs, convert, convert_to, cutsat, dbg_trace, decide, decreasing_tactic, decreasing_trivial, decreasing_trivial_pre_omega, decreasing_with, delta, deriving_LawfulEq_tactic, deriving_LawfulEq_tactic_step, deriving_ReflEq_tactic, discrete_cases, done, dsimp, dsimp!, dsimp?, dsimp?!, eapply, econstructor, else, else, enat_to_nat, eq_refl, erw, erw?, eta_expand, eta_reduce, eta_struct, exact, exact?, exact_mod_cast, exacts, exfalso, exists, existsi, expose_names, ext, ext1, extract_goal, extract_lets, fail, fail_if_no_progress, fail_if_success, false_or_by_contra, fapply, fconstructor, field, field_simp, field_simp_discharge, filter_upwards, fin_cases, fin_omega, find, finiteness, finiteness?, finiteness_nonterminal, first, focus, forward, forward?, frac_tac, fun_cases, fun_induction, fun_prop, funext, gcongr, gcongr?, gcongr_discharger, generalize, generalize', generalize_proofs, get_elem_tactic, get_elem_tactic_extensible, get_elem_tactic_trivial, ghost_calc, ghost_fun_tac, ghost_simp, grewrite, grind, grind?, grobner, group, grw, guard_expr, guard_goal_nums, guard_hyp, guard_hyp_nums, guard_target, have, have, have', haveI, hint, induction, induction', infer_instance, infer_param, inhabit, init_ring, injection, injections, interval_cases, intro, intro, intro, intros, introv, isBoundedDefault, itauto, itauto!, iterate, left, let, let, let, let', letI, let_to_have, lia, lift, lift_lets, liftable_prefixes, linarith, linarith!, linarith?, linarith?!, linear_combination, linear_combination', linear_combination2, map_fun_tac, map_tacs, massumption, massumption, match, match, match_scalars, match_target, mcases, mcases, mclear, mclear, mconstructor, mconstructor, mdup, measurability, measurability!, measurability!?, measurability?, mem_tac, mem_tac_aux, mexact, mexact, mexfalso, mexfalso, mexists, mexists, mfld_set_tac, mframe, mframe, mhave, mhave, mintro, mintro, mleave, mleave, mleft, mleft, mod_cases, module, monicity, monicity!, mono, monoidal, monoidal_coherence, monoidal_coherence, monoidal_nf, monoidal_simps, move_add, move_mul, move_oper, mpure, mpure, mpure_intro, mpure_intro, mrefine, mrefine, mrename_i, mrename_i, mreplace, mreplace, mrevert, mrevert, mright, mright, mspec, mspec, mspec_no_bind, mspec_no_simp, mspecialize, mspecialize, mspecialize_pure, mspecialize_pure, mstart, mstart, mstop, mstop, mv_bisim, mvcgen, mvcgen, mvcgen?, mvcgen_trivial, mvcgen_trivial_extensible, native_decide, next, nlinarith, nlinarith!, nofun, nomatch, noncomm_ring, nontriviality, norm_cast, norm_cast0, norm_num, norm_num1, nth_grewrite, nth_grw, nth_rewrite, nth_rw, observe, observe?, observe?, obtain, omega, on_goal, open, order, order_core, peel, pgame_wf_tac, pi_lower_bound, pi_upper_bound, pick_goal, plausible, pnat_positivity, pnat_to_nat, polyrith, positivity, pull, pure_coherence, push, push_cast, push_neg, qify, rcases, rcongr, recover, reduce, reduce_mod_char, reduce_mod_char!, refine, refine', refine_lift, refine_lift', refold_let, rel, rename, rename', rename_bvar, rename_i, repeat, repeat', repeat1, repeat1', replace, replace, restrict_tac, restrict_tac?, revert, rewrite, rewrite!, rfl, rfl', rfl_cat, rify, right, ring, ring!, ring1, ring1!, ring1_nf, ring1_nf!, ring_nf, ring_nf!, rintro, rotate_left, rotate_right, rsuffices, run_tac, rw, rw!, rw?, rw??, rw_mod_cast, rw_search, rwa, saturate, saturate?, says, set, set!, set_option, show, show_term, simp, simp!, simp?, simp?!, simp_all, simp_all!, simp_all?, simp_all?!, simp_all_arith, simp_all_arith!, simp_arith, simp_arith!, simp_intro, simp_rw, simp_wf, simpa, simpa!, simpa?, simpa?!, sizeOf_list_dec, skip, sleep, sleep_heartbeats, slice_lhs, slice_rhs, smul_tac, solve, solve_by_elim, sorry, sorry_if_sorry, specialize, specialize_all, split, split_ands, split_ifs, squeeze_scope, stop, subsingleton, subst, subst_eqs, subst_hom_lift, subst_vars, substs, success_if_fail_with_msg, suffices, suffices, suggestions, swap, swap_var, symm, symm_saturate, tauto, tauto_set, tfae_finish, tfae_have, tfae_have, toFinite_tac, to_encard_tac, trace, trace, trace_state, trans, transitivity, triv, trivial, try, try?, try_suggestions, try_this, type_check, unfold, unfold?, unfold_projs, unhygienic, uniqueDiffWithinAt_Ici_Iic_univ, unit_interval, unreachable!, use, use!, use_discharger, use_finite_instance, valid, volume_tac, wait_for_unblock_async, whisker_simps, whnf, with_panel_widgets, with_reducible, with_reducible_and_instances, with_unfolding_all, witt_truncateFun_tac, wlog, wlog!, zify
</div>


```lean
#help tactic apply -- tells you about a specific tactic
```

Entering Tactic Mode
===

Tactic mode is entered in a proof using the keyword `by`

```lean
variable (p : Type → Prop)

theorem my_thm1 : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by <proofstate>['p : Type → Prop\n⊢ (¬∃ x, p x) ↔ ∀ (x : Type), ¬p x']</proofstate>
  sorry
```

Here, `sorry` is a tactic that closes the proof, but uses the `sorryAx` axiom.
Lean underlines the theorem name to denote that you still have work to do.

```lean
#help tactic sorry

#print axioms my_thm1   -- 'LeanW26.my_thm' depends on axioms: [sorryAx]
```

Tactics Produce Terms
===

Tactics produce terms that are then type checked by the kernel. 
```lean
theorem t (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4* z < 0)
  : False := by <proofstate>['x y z : ℚ\nh1 : 2 * x < 3 * y\nh2 : -4 * x + 2 * z < 0\nh3 : 12 * y - 4 * z < 0\n⊢ False']</proofstate>
  linarith

#print t
```
<div style='font-family: monospace; font-size: 4pt'>
 fun x y z h1 h2 h3 ↦ False.elim (Linarith.lt_irrefl (Eq.mp (congrArg (fun _a ↦ _a < 0) (Ring.of_eq (Ring.add_congr (Ring.add_congr (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 4))) (Ring.sub_congr (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 2))) (Ring.atom_pf x) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right x (Nat.rawCast 1) (Ring.mul_one (Nat.rawCast 2))) (Ring.mul_zero (Nat.rawCast 2)) (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))) (Ring.zero_mul (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))) (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 3))) (Ring.atom_pf y) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right y (Nat.rawCast 1) (Ring.mul_one (Nat.rawCast 3))) (Ring.mul_zero (Nat.rawCast 3)) (Ring.add_pf_add_zero (y ^ Nat.rawCast 1 * Nat.rawCast 3 + 0))) (Ring.zero_mul (y ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Ring.add_pf_add_zero (y ^ Nat.rawCast 1 * Nat.rawCast 3 + 0)))) (Ring.sub_pf (Ring.neg_add (Ring.neg_mul y (Nat.rawCast 1) (Ring.neg_one_mul (Meta.NormNum.IsInt.to_raw_eq (Meta.NormNum.isInt_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 1)) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 3)) (Eq.refl (Int.negOfNat 3)))))) Ring.neg_zero) (Ring.add_pf_add_lt (x ^ Nat.rawCast 1 * Nat.rawCast 2) (Ring.add_pf_zero_add (y ^ Nat.rawCast 1 * (Int.negOfNat 3).rawCast + 0))))) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right x (Nat.rawCast 1) (Meta.NormNum.IsNat.to_raw_eq (Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsNat.of_raw ℚ 4) (Meta.NormNum.IsNat.of_raw ℚ 2) (Eq.refl 8)))) (Ring.mul_add (Ring.mul_pf_right y (Nat.rawCast 1) (Meta.NormNum.IsInt.to_raw_eq (Meta.NormNum.isInt_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 4)) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 3)) (Eq.refl (Int.negOfNat 12))))) (Ring.mul_zero (Nat.rawCast 4)) (Ring.add_pf_add_zero (y ^ Nat.rawCast 1 * (Int.negOfNat 12).rawCast + 0))) (Ring.add_pf_add_lt (x ^ Nat.rawCast 1 * Nat.rawCast 8) (Ring.add_pf_zero_add (y ^ Nat.rawCast 1 * (Int.negOfNat 12).rawCast + 0)))) (Ring.zero_mul (x ^ Nat.rawCast 1 * Nat.rawCast 2 + (y ^ Nat.rawCast 1 * (Int.negOfNat 3).rawCast + 0))) (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * Nat.rawCast 8 + (y ^ Nat.rawCast 1 * (Int.negOfNat 12).rawCast + 0))))) (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 2))) (Ring.sub_congr (Ring.add_congr (Ring.mul_congr (Ring.neg_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 4))) (Ring.neg_add (Ring.neg_one_mul (Meta.NormNum.IsInt.to_raw_eq (Meta.NormNum.isInt_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 1)) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 4)) (Eq.refl (Int.negOfNat 4))))) Ring.neg_zero)) (Ring.atom_pf x) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right x (Nat.rawCast 1) (Ring.mul_one (Int.negOfNat 4).rawCast)) (Ring.mul_zero (Int.negOfNat 4).rawCast) (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast + 0))) (Ring.zero_mul (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast + 0)))) (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 2))) (Ring.atom_pf z) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right z (Nat.rawCast 1) (Ring.mul_one (Nat.rawCast 2))) (Ring.mul_zero (Nat.rawCast 2)) (Ring.add_pf_add_zero (z ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))) (Ring.zero_mul (z ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Ring.add_pf_add_zero (z ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))) (Ring.add_pf_add_lt (x ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast) (Ring.add_pf_zero_add (z ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))) (Ring.cast_zero (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 0))) (Ring.sub_pf Ring.neg_zero (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast + (z ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right x (Nat.rawCast 1) (Meta.NormNum.IsInt.to_raw_eq (Meta.NormNum.isInt_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 2)) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 4)) (Eq.refl (Int.negOfNat 8))))) (Ring.mul_add (Ring.mul_pf_right z (Nat.rawCast 1) (Meta.NormNum.IsNat.to_raw_eq (Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsNat.of_raw ℚ 2) (Meta.NormNum.IsNat.of_raw ℚ 2) (Eq.refl 4)))) (Ring.mul_zero (Nat.rawCast 2)) (Ring.add_pf_add_zero (z ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))) (Ring.add_pf_add_lt (x ^ Nat.rawCast 1 * (Int.negOfNat 8).rawCast) (Ring.add_pf_zero_add (z ^ Nat.rawCast 1 * Nat.rawCast 4 + 0)))) (Ring.zero_mul (x ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast + (z ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))) (Ring.add_pf_add_zero (x ^ Nat.rawCast 1 * (Int.negOfNat 8).rawCast + (z ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))))) (Ring.add_pf_add_overlap_zero (Ring.add_overlap_pf_zero x (Nat.rawCast 1) (Meta.NormNum.IsInt.to_isNat (Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 8)) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 8)) (Eq.refl (Int.ofNat 0))))) (Ring.add_pf_add_lt (y ^ Nat.rawCast 1 * (Int.negOfNat 12).rawCast) (Ring.add_pf_zero_add (z ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))))) (Ring.sub_congr (Ring.sub_congr (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 12))) (Ring.atom_pf y) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right y (Nat.rawCast 1) (Ring.mul_one (Nat.rawCast 12))) (Ring.mul_zero (Nat.rawCast 12)) (Ring.add_pf_add_zero (y ^ Nat.rawCast 1 * Nat.rawCast 12 + 0))) (Ring.zero_mul (y ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Ring.add_pf_add_zero (y ^ Nat.rawCast 1 * Nat.rawCast 12 + 0)))) (Ring.mul_congr (Ring.cast_pos (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 4))) (Ring.atom_pf z) (Ring.add_mul (Ring.mul_add (Ring.mul_pf_right z (Nat.rawCast 1) (Ring.mul_one (Nat.rawCast 4))) (Ring.mul_zero (Nat.rawCast 4)) (Ring.add_pf_add_zero (z ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))) (Ring.zero_mul (z ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Ring.add_pf_add_zero (z ^ Nat.rawCast 1 * Nat.rawCast 4 + 0)))) (Ring.sub_pf (Ring.neg_add (Ring.neg_mul z (Nat.rawCast 1) (Ring.neg_one_mul (Meta.NormNum.IsInt.to_raw_eq (Meta.NormNum.isInt_mul (Eq.refl HMul.hMul) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 1)) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 4)) (Eq.refl (Int.negOfNat 4)))))) Ring.neg_zero) (Ring.add_pf_add_lt (y ^ Nat.rawCast 1 * Nat.rawCast 12) (Ring.add_pf_zero_add (z ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast + 0))))) (Ring.cast_zero (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 0))) (Ring.sub_pf Ring.neg_zero (Ring.add_pf_add_zero (y ^ Nat.rawCast 1 * Nat.rawCast 12 + (z ^ Nat.rawCast 1 * (Int.negOfNat 4).rawCast + 0))))) (Ring.add_pf_add_overlap_zero (Ring.add_overlap_pf_zero y (Nat.rawCast 1) (Meta.NormNum.IsInt.to_isNat (Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 12)) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 12)) (Eq.refl (Int.ofNat 0))))) (Ring.add_pf_add_overlap_zero (Ring.add_overlap_pf_zero z (Nat.rawCast 1) (Meta.NormNum.IsInt.to_isNat (Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd) (Meta.NormNum.IsNat.to_isInt (Meta.NormNum.IsNat.of_raw ℚ 4)) (Meta.NormNum.IsInt.of_raw ℚ (Int.negOfNat 4)) (Eq.refl (Int.ofNat 0))))) (Ring.add_pf_zero_add 0)))) (Ring.cast_zero (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 0))))) (Linarith.add_neg (Linarith.add_neg (Linarith.mul_neg (Linarith.sub_neg_of_lt h1) (Meta.NormNum.isNat_lt_true (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 0)) (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 4)) (Eq.refl false))) (Linarith.mul_neg (Linarith.sub_neg_of_lt h2) (Meta.NormNum.isNat_lt_true (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 0)) (Meta.NormNum.isNat_ofNat ℚ (Eq.refl 2)) (Eq.refl false)))) (Linarith.sub_neg_of_lt h3)))) </div>



intro
===

Introduction applies to implications and forall statements, introducing either a new
hypothesis or a new object. It takes the place of `fun h₁ h₂ ... => ...`  
```lean
example : (¬ ∃ x, p x) → (∀ x, ¬ p x) := by <proofstate>['p : Type → Prop\n⊢ (¬∃ x, p x) → ∀ (x : Type), ¬p x']</proofstate>
  intro hnep x <proofstate>['p : Type → Prop\nhnep : ¬∃ x, p x\nx : Type\n⊢ ¬p x']</proofstate>
  sorry                -- ⊢ ¬p x
```

apply
===

The `apply` tactic applies a function, for-all statement, or another theorem.
It looks for arguments that match its type signature in the context and
automatically uses them if possible. 
```lean
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by <proofstate>['p : Type → Prop\n⊢ (¬∃ x, p x) ↔ ∀ (x : Type), ¬p x']</proofstate>
  apply Iff.intro <proofstate>['case mp\np : Type → Prop\n⊢ (¬∃ x, p x) → ∀ (x : Type), ¬p x', 'case mpr\np : Type → Prop\n⊢ (∀ (x : Type), ¬p x) → ¬∃ x, p x']</proofstate>
  · intro h x hp               --  ⊢ False <proofstate>['case mp\np : Type → Prop\nh : ¬∃ x, p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    apply h                    --  ⊢ ∃ x, p x <proofstate>['case mp\np : Type → Prop\nh : ¬∃ x, p x\nx : Type\nhp : p x\n⊢ ∃ x, p x']</proofstate>
    apply Exists.intro x       --  ⊢ p x <proofstate>['case mp\np : Type → Prop\nh : ¬∃ x, p x\nx : Type\nhp : p x\n⊢ p x']</proofstate>
    apply hp                   --  Goals accomplished!
  · intro hnpx h <proofstate>['case mpr\np : Type → Prop\nhnpx : ∀ (x : Type), ¬p x\nh : ∃ x, p x\n⊢ False']</proofstate>
    apply Exists.elim h <proofstate>['case mpr\np : Type → Prop\nhnpx : ∀ (x : Type), ¬p x\nh : ∃ x, p x\n⊢ ∀ (a : Type), p a → False']</proofstate>
    intro x hp <proofstate>['case mpr\np : Type → Prop\nhnpx : ∀ (x : Type), ¬p x\nh : ∃ x, p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    apply hnpx x <proofstate>['case mpr\np : Type → Prop\nhnpx : ∀ (x : Type), ¬p x\nh : ∃ x, p x\nx : Type\nhp : p x\n⊢ p x']</proofstate>
    apply hp
```
 The dots (entered as `\.`) help deliniate the subcases, isolating them in the Infoview.

This tactic proof compiles to the term level proof
```lean
fun p ↦ {
  mp := fun h x hp ↦ h (Exists.intro x hp),
  mpr := fun h hepx ↦ Exists.elim hepx fun x hpa ↦ h x hpa
}
```


apply with Other Theorems
===

You can use `apply` with previously defined theorems.


```lean
theorem my_thm2 (q : Prop) : q → q := id

example (q : ℕ → Prop) : (∀ x, q x) → ∀ x, q x := by <proofstate>['p : Type → Prop\nq : ℕ → Prop\n⊢ (∀ (x : ℕ), q x) → ∀ (x : ℕ), q x']</proofstate>
  apply my_thm2

#check Eq.symm  -- defined in Init.Prelude

example (x y : ℕ) : x = y → y = x := by <proofstate>['p : Type → Prop\nx y : ℕ\n⊢ x = y → y = x']</proofstate>
  apply Eq.symm
```
 If you are stuck, there is `apply?` 
```lean
example (x y : ℕ) : x = y → y = x := by <proofstate>['p : Type → Prop\nx y : ℕ\n⊢ x = y → y = x']</proofstate>
  apply?         -- Try this:
                 --   [apply] exact fun a ↦ id
                 -- (Eq.symm a)
```
 If you click on `[apply]` VS Code inserts the suggested proof (which
in this case isn't particuarly concise, but it works).

exact
===

`exact` is a variant of apply that requires you to fill in the arguments you are using.
It essentially pops you out of tactic mode. It is used at the end of proofs to make things
more clear and robust to changes in how other tactics in the proof are applied.

Here is the previous proof presented more compactly. 
```lean
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by <proofstate>['p : Type → Prop\n⊢ (¬∃ x, p x) ↔ ∀ (x : Type), ¬p x']</proofstate>
  apply Iff.intro <proofstate>['case mp\np : Type → Prop\n⊢ (¬∃ x, p x) → ∀ (x : Type), ¬p x', 'case mpr\np : Type → Prop\n⊢ (∀ (x : Type), ¬p x) → ¬∃ x, p x']</proofstate>
  · intro h x hp <proofstate>['case mp\np : Type → Prop\nh : ¬∃ x, p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    exact h (Exists.intro x hp)
  · intro h hepx <proofstate>['case mpr\np : Type → Prop\nh : ∀ (x : Type), ¬p x\nhepx : ∃ x, p x\n⊢ False']</proofstate>
    apply Exists.elim hepx <proofstate>['case mpr\np : Type → Prop\nh : ∀ (x : Type), ¬p x\nhepx : ∃ x, p x\n⊢ ∀ (a : Type), p a → False']</proofstate>
    intro x hpa <proofstate>['case mpr\np : Type → Prop\nh : ∀ (x : Type), ¬p x\nhepx : ∃ x, p x\nx : Type\nhpa : p x\n⊢ False']</proofstate>
    exact (h x) hpa
```
 And even more compactly using structure notation and matching 
```lean
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by <proofstate>['p : Type → Prop\n⊢ (¬∃ x, p x) ↔ ∀ (x : Type), ¬p x']</proofstate>
  apply Iff.intro <proofstate>['case mp\np : Type → Prop\n⊢ (¬∃ x, p x) → ∀ (x : Type), ¬p x', 'case mpr\np : Type → Prop\n⊢ (∀ (x : Type), ¬p x) → ¬∃ x, p x']</proofstate>
  · intro h x hp <proofstate>['case mp\np : Type → Prop\nh : ¬∃ x, p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    exact h ⟨ x, hp ⟩
  · intro h ⟨ x, hp ⟩ <proofstate>['case mpr\np : Type → Prop\nh : ∀ (x : Type), ¬p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    exact (h x) hp
```

use
===
apply `Exists.intro x` is quite common. The tactic `use` wraps it.

```lean
example : ∀ (x : ℕ), ∃ y, x < y := by <proofstate>['p : Type → Prop\n⊢ ∀ (x : ℕ), ∃ y, x < y']</proofstate>
  intro x <proofstate>['p : Type → Prop\nx : ℕ\n⊢ ∃ y, x < y']</proofstate>
  use x+1 <proofstate>['case h\np : Type → Prop\nx : ℕ\n⊢ x < x + 1']</proofstate>
  apply?       -- Try this:
               --   [apply] exact lt_add_one x

example : ∀ (x : ℕ), ∃ y, x < y := by <proofstate>['p : Type → Prop\n⊢ ∀ (x : ℕ), ∃ y, x < y']</proofstate>
  intro x <proofstate>['p : Type → Prop\nx : ℕ\n⊢ ∃ y, x < y']</proofstate>
  use x+1 <proofstate>['case h\np : Type → Prop\nx : ℕ\n⊢ x < x + 1']</proofstate>
  exact lt_add_one x
```
 `use` allows for multiple introductions at the same time
```lean
example : ∃ (x:ℕ), ∃ y, x < y := by <proofstate>['p : Type → Prop\n⊢ ∃ x y, x < y']</proofstate>
  use 0, 1 <proofstate>['case h\np : Type → Prop\n⊢ 0 < 1']</proofstate>
  exact Nat.one_pos
```

assumption
===

This tactic looks through the context to find an assumption that applies,
and applies it. It is like apply but where you don't have to say what to apply. 
```lean
example (c : Type) (h : p c) : ∃ x, p x := by <proofstate>['p : Type → Prop\nc : Type\nh : p c\n⊢ ∃ x, p x']</proofstate>
  apply Exists.intro c <proofstate>['p : Type → Prop\nc : Type\nh : p c\n⊢ p c']</proofstate>
  assumption
```

Exercises
===

<ex /> Do the following proofs using the tactics `intro`, `apply` and `use` along with the
basic inductive definitions and eliminators for `And` and `Or`. 
```lean
variable (P Q : Type → Prop)

example : (∃ x, P x ∧ Q x) →  ∃ x, Q x ∧ P x := sorry

example : (∃ x, P x ∨ Q x) →  ∃ x, Q x ∨ P x := sorry
```

FOL Examples Revisited
===

Now that we can use tactics, our First Order Logic Proofs can be made to look a little
cleaner, although one might argue the use of angled brackets is harder to read. 
```lean
variable (p : Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by <proofstate>['p✝ P Q p : Type → Prop\nr : Prop\n⊢ (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r']</proofstate>
  apply Iff.intro <proofstate>['case mp\np✝ P Q p : Type → Prop\nr : Prop\n⊢ (∃ x, p x ∧ r) → (∃ x, p x) ∧ r', 'case mpr\np✝ P Q p : Type → Prop\nr : Prop\n⊢ (∃ x, p x) ∧ r → ∃ x, p x ∧ r']</proofstate>
  · intro ⟨ x, ⟨ hx, hr ⟩ ⟩ <proofstate>['case mp\np✝ P Q p : Type → Prop\nr : Prop\nx : Type\nhx : p x\nhr : r\n⊢ (∃ x, p x) ∧ r']</proofstate>
    exact ⟨ ⟨ x, hx ⟩ , hr ⟩
  · intro ⟨ ⟨ x, hx ⟩ , hr ⟩ <proofstate>['case mpr\np✝ P Q p : Type → Prop\nr : Prop\nx : Type\nhx : p x\nhr : r\n⊢ ∃ x, p x ∧ r']</proofstate>
    exact ⟨ x, ⟨ hx, hr ⟩ ⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by <proofstate>['p✝ P Q p : Type → Prop\nr : Prop\n⊢ (¬∃ x, p x) ↔ ∀ (x : Type), ¬p x']</proofstate>
  apply Iff.intro <proofstate>['case mp\np✝ P Q p : Type → Prop\nr : Prop\n⊢ (¬∃ x, p x) → ∀ (x : Type), ¬p x', 'case mpr\np✝ P Q p : Type → Prop\nr : Prop\n⊢ (∀ (x : Type), ¬p x) → ¬∃ x, p x']</proofstate>
  · intro h x hp <proofstate>['case mp\np✝ P Q p : Type → Prop\nr : Prop\nh : ¬∃ x, p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    exact h ⟨ x, hp ⟩
  · intro h ⟨ x, hp ⟩ <proofstate>['case mpr\np✝ P Q p : Type → Prop\nr : Prop\nh : ∀ (x : Type), ¬p x\nx : Type\nhp : p x\n⊢ False']</proofstate>
    exact h x hp
```

`have` and `let`
===

You can use `have` to record intermediate results 
```lean
example (p q : Prop) : p ∧ q → p ∨ q := by <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\n⊢ p ∧ q → p ∨ q']</proofstate>
  intro ⟨ h1, h2 ⟩ <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh1 : p\nh2 : q\n⊢ p ∨ q']</proofstate>
  have hp : p := h1 <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh1 : p\nh2 : q\nhp : p\n⊢ p ∨ q']</proofstate>
  exact Or.inl hp
```
 If you need an intermediate value, you should use `let`. 
```lean
example : ∃ n , n > 0 := by <proofstate>['p✝ P Q p : Type → Prop\nr : Prop\n⊢ ∃ n, n > 0']</proofstate>
  let m := 1 <proofstate>['p✝ P Q p : Type → Prop\nr : Prop\nm : ℕ := 1\n⊢ ∃ n, n > 0']</proofstate>
  exact ⟨ m, Nat.one_pos ⟩
```

cases
===

The `cases` tactic wraps around `Or.elim` to make proofs easier to read. For example, 
```lean
example (p q : Prop) : (p ∨ q) → q ∨ p  := by <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\n⊢ p ∨ q → q ∨ p']</proofstate>
  intro h <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\n⊢ q ∨ p']</proofstate>
  apply Or.elim h <proofstate>['case left\np✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\n⊢ p → q ∨ p', 'case right\np✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\n⊢ q → q ∨ p']</proofstate>
  · intro hp <proofstate>['case left\np✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\nhp : p\n⊢ q ∨ p']</proofstate>
    exact Or.symm h
  · intro hq <proofstate>['case right\np✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\nhq : q\n⊢ q ∨ p']</proofstate>
    exact Or.symm h
```
 Becomes 
```lean
example (p q : Prop) : (p ∨ q) → q ∨ p  := by <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\n⊢ p ∨ q → q ∨ p']</proofstate>
  intro h <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\n⊢ q ∨ p']</proofstate>
  cases h with <proofstate>['p✝¹ P Q p✝ : Type → Prop\nr p q : Prop\nh : p ∨ q\n⊢ q ∨ p']</proofstate>
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.symm (Or.inr hq)
```

Cases Works With any Inductive Type
===

Here's are some alternative ways to prove some simple results 
```lean
variable (P Q : Type → Prop)
```
 Cases on an Exists structure 
```lean
example : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\n⊢ (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x']</proofstate>
  intro h <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\nh : ∃ x, P x ∧ Q x\n⊢ ∃ x, Q x ∧ P x']</proofstate>
  cases h with <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\nh : ∃ x, P x ∧ Q x\n⊢ ∃ x, Q x ∧ P x']</proofstate>
  | intro x h => exact ⟨ x, And.symm h ⟩
```
 Cases on an And structure 
```lean
example (p q : Prop) : (p ∧ q) → (p ∨ q) :=  by <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Prop\n⊢ p ∧ q → p ∨ q']</proofstate>
  intro h <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Prop\nh : p ∧ q\n⊢ p ∨ q']</proofstate>
  cases h with <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Prop\nh : p ∧ q\n⊢ p ∨ q']</proofstate>
  | intro hp hq => exact Or.inl hp
```

nomatch Revisited
===

We defined using `nomatch`.

```lean
def False.elim {p : Prop} (h : False) : p :=
  nomatch h
```
 We could have used the `cases` tactic, which finds no cases and
produces a term. 
```lean
def False.elim' {p : Prop} (h : False) : p :=
  by cases h
  -- ... no cases
```
 The term level proov uses t version of the recursor for `False` 
```lean
#print False.elim'   -- fun {p} h ↦ False.casesOn (fun t ↦ h = t → p) h (Eq.refl h)

#check False.casesOn       -- False.casesOn.{u} (motive : False → Sort u) (t : False)
                           -- : motive t

#check False.recOn         -- False.recOn.{u} (motive : False → Sort u) (t : False)
                           -- : motive t
```

Cases with Person
===

```lean
--hide
inductive Person where | mary | steve | ed | jolin

open Person
--unhide
```
 Recall that `on_right` was defined as 
```lean
def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary
```
 We can do a proof by cases with `Person` using the `cases` tactic 
```lean
example : ∀ x : Person, ∃ y, ¬on_right x y := by <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\n⊢ ∀ (x : Person), ∃ y, ¬on_right x y']</proofstate>
  intro hp <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\nhp : Person\n⊢ ∃ y, ¬on_right hp y']</proofstate>
  cases hp with <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\nhp : Person\n⊢ ∃ y, ¬on_right hp y']</proofstate>
  | mary =>                 -- ⊢ ∃ y, ¬on_right mary y <proofstate>['case mary\np✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\n⊢ ∃ y, ¬on_right mary y']</proofstate>
    use jolin               -- ⊢ ¬on_right mary jolin <proofstate>['case h\np✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\n⊢ ¬on_right mary jolin']</proofstate>
    intro h                 -- on_right mary jolin ⊢ False <proofstate>['case h\np✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\nh : on_right mary jolin\n⊢ False']</proofstate>
    cases h                 -- Subgoal accomplished
                            -- There are no cases in which on_right mary jolin is true
  | steve => sorry
  | ed => sorry
  | jolin => sorry
```

`by_cases`
===

The `cases` tactic is not to be confused with the `by_cases` tactic,
may use resort to classical reasoning. 
```lean
theorem cases_example (p : Prop) : p ∨ ¬p := by <proofstate>['p : Prop\n⊢ p ∨ ¬p']</proofstate>
  by_cases h : p <proofstate>['case pos\np : Prop\nh : p\n⊢ p ∨ ¬p', 'case neg\np : Prop\nh : ¬p\n⊢ p ∨ ¬p']</proofstate>
  · exact Or.inl h -- show p ∨ ¬p assuming h : p
  · exact Or.inr h -- show p ∨ ¬p assuming h : ¬p

#print axioms cases_example    --  [propext, Classical.choice, Quot.sound]
```
 However, `by_cases` on a non-prop usually does not require classical reasoning. 
```lean
theorem another_example : ∀ n : ℕ, n = 0 ∨ n > 0 := by <proofstate>['⊢ ∀ (n : ℕ), n = 0 ∨ n > 0']</proofstate>
  intro n <proofstate>['n : ℕ\n⊢ n = 0 ∨ n > 0']</proofstate>
  by_cases h : n = 0 <proofstate>['case pos\nn : ℕ\nh : n = 0\n⊢ n = 0 ∨ n > 0', 'case neg\nn : ℕ\nh : ¬n = 0\n⊢ n = 0 ∨ n > 0']</proofstate>
  · exact Or.inl h
  · apply Or.inr <proofstate>['case neg.h\nn : ℕ\nh : ¬n = 0\n⊢ n > 0']</proofstate>
    exact Nat.zero_lt_of_ne_zero h     -- obtained via apply?

#print axioms another_example      -- does not depend on any axioms
```

Unfolding
===

Recall the definition


```lean
def next_to (p q : Person) := on_right p q ∨ on_right q p
```

We might encounter `next_to` in a proof and want to replace it with its definition.

```lean
example : ∀ p , ∀ q , (on_right p q) → next_to p q := by <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\n⊢ ∀ (p q : Person), on_right p q → next_to p q']</proofstate>
  intro p q h <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Person\nh : on_right p q\n⊢ next_to p q']</proofstate>
  unfold next_to             -- helps us see what we have to do <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Person\nh : on_right p q\n⊢ on_right p q ∨ on_right q p']</proofstate>
  exact Or.inl h
```

Exercise
===

<ex /> Prove the following.


```lean
example : ∀ p : Person, ∃ q : Person, next_to p q := sorry
example : ∀ p : Person, ∃ q : Person, ¬next_to p q := sorry
```

Induction
===

Consider the natural numbers and suppose `P : Nat → Prop` is a
property. To prove `P` with induction, you prove `P(0)` and `∀ n, P(n) → P(n+1)`. 
```lean
def E (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ x => ¬E x

theorem even_or_even_succ : ∀ n : Nat, E n ∨ E n.succ := by <proofstate>['⊢ ∀ (n : ℕ), E n ∨ E n.succ']</proofstate>
  intro n <proofstate>['n : ℕ\n⊢ E n ∨ E n.succ']</proofstate>
  induction n with <proofstate>['n : ℕ\n⊢ E n ∨ E n.succ']</proofstate>
  | zero => exact Or.inl True.intro
  | succ k ih => <proofstate>['case succ\nk : ℕ\nih : E k ∨ E k.succ\n⊢ E (k + 1) ∨ E (k + 1).succ']</proofstate>
    apply Or.elim ih                           -- ih : E k ∨ E k.succ <proofstate>['case succ.left\nk : ℕ\nih : E k ∨ E k.succ\n⊢ E k → E (k + 1) ∨ E (k + 1).succ', 'case succ.right\nk : ℕ\nih : E k ∨ E k.succ\n⊢ E k.succ → E (k + 1) ∨ E (k + 1).succ']</proofstate>
    · intro h                                  -- h  : E k <proofstate>['case succ.left\nk : ℕ\nih : E k ∨ E k.succ\nh : E k\n⊢ E (k + 1) ∨ E (k + 1).succ']</proofstate>
      exact Or.inr (fun a => a h)              -- ⊢ E (k + 1) ∨ E (k + 1).succ
    · intro h <proofstate>['case succ.right\nk : ℕ\nih : E k ∨ E k.succ\nh : E k.succ\n⊢ E (k + 1) ∨ E (k + 1).succ']</proofstate>
      exact Or.inl h
```

The `induction` tactic is essentialy a front end to the recursor.

```lean
#print even_or_even_succ    -- ∀ (n : ℕ), E n ∨ E n.succ :=
                            -- fun n ↦ Nat.recAux (Or.inl True.intro)
                            -- (fun k ih ↦ Or.elim ih (fun h ↦ Or.inr
                            -- fun a ↦ a h) fun h ↦ Or.inl h) n
```

Induction on any Inductive Type
===

The `induction` tactic behaves like `cases` when there are no inductive
steps. But the opposite is not true.


```lean
example {p q : Prop} : p ∧ q → q ∧ p := by <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Prop\n⊢ p ∧ q → q ∧ p']</proofstate>
  intro hpq <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Prop\nhpq : p ∧ q\n⊢ q ∧ p']</proofstate>
  induction hpq with <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np q : Prop\nhpq : p ∧ q\n⊢ q ∧ p']</proofstate>
  | intro left right => exact ⟨ right, left ⟩

example {p : ℕ → Prop} : (∃ x, ¬p x) → ¬∀ x, p x := by <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np : ℕ → Prop\n⊢ (∃ x, ¬p x) → ¬∀ (x : ℕ), p x']</proofstate>
  intro h1 h2 <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np : ℕ → Prop\nh1 : ∃ x, ¬p x\nh2 : ∀ (x : ℕ), p x\n⊢ False']</proofstate>
  induction h1 with <proofstate>['p✝¹ P✝ Q✝ p✝ : Type → Prop\nr : Prop\nP Q : Type → Prop\np : ℕ → Prop\nh1 : ∃ x, ¬p x\nh2 : ∀ (x : ℕ), p x\n⊢ False']</proofstate>
  | intro w h => exact h (h2 w)


--hide
inductive PreDyadic where
  | zero    : PreDyadic
  | add_one : PreDyadic → PreDyadic  -- x ↦ x + 1
  | half    : PreDyadic → PreDyadic  -- x ↦ x / 2
  | neg     : PreDyadic → PreDyadic  -- x ↦ -x

open PreDyadic

def PreDyadic.double (x : PreDyadic) : PreDyadic := match x with
  | PreDyadic.zero =>  PreDyadic.zero
  | add_one x => add_one (add_one (double x))   -- 2(x+1) = 2x+2
  | half x =>  x                                -- 2(x/2) = x
  | neg  x  => neg (double x)

def PreDyadic.add (x y : PreDyadic) : PreDyadic := match x with
  | PreDyadic.zero => y
  | add_one z =>  (add z y).add_one  -- (z+1) + y = z+y + 1,  a/(2^n) --> (a+2^n)/(2^n)
  | half z => (add z y.double).half  -- z/2 + y = (z+2y)/2
  | neg z => (add z y.neg).neg       -- (-z)+y = -(z+(-y))

def PreDyadic.mul (x y : PreDyadic) : PreDyadic := match x with
  | PreDyadic.zero => zero
  | add_one z =>  add (mul z y) y    -- (z+1)*y = z*y + y
  | half z => (mul z y).half         -- (z/2)*y = (z*y)/2
  | neg z => (mul z y).neg
--unhide
```

Exercise
===

<ex /> Recall the definition of `PreDyadic`.

a) Define a function


```lean
def no_negs ( x : PreDyadic ) : Prop := sorry
```
 that is `True` when `x` has no `neg` constructors used to define it.

b) Prove


```lean
example (x : PreDyadic) : no_negs x → no_negs (double x) := sorry
```

c) Prove

```lean
example (x y : PreDyadic) : no_negs x → no_negs y → no_negs (mul x y) := sorry
```

Exercise
===

<ex /> Scan through the list of tactics using:


```lean
#help tactic
```
 which puts all the tactics in the Infoview. Make sure that mathlib is imported, or this doesn't work.

Choose a tactic that looks interesting and come up with two examples of its use in simple proofs. Use `#print` to print out your proofs to see what terms are generated. Finally , for each example, explain to the best of your understanding what the tactic is doing.


Defining New Tactics
===

You can define your own tactics. Here is an example. We will cover this
and other "meta-programming" methods later. You will need to `import Lean`.


```lean
open Lean Elab Tactic

syntax (name := myTacticSyntax) "my_tactic" : tactic

@[tactic myTacticSyntax]
def myTactic : Tactic := fun _ => do
  try
    evalTactic (← `(tactic| rfl))      -- Put any  logic you want
                                       -- here, including inspecting the
                                       -- context, expressions, low level
                                       -- syntax, etc.
  catch _ =>
    throwError "my_tactic: could not solve the goal"

example : 0 = 0 := by <proofstate>['p✝ P✝ Q✝ p : Type → Prop\nr : Prop\nP Q : Type → Prop\n⊢ 0 = 0']</proofstate>
  my_tactic             -- yay it works!
```

It only works when rfl does though.
```lean
example (p : Prop) : p := by my_tactic      -- my_tactic: could not solve the goal
```

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

