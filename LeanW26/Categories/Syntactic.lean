import Mathlib
import LeanW26.Categories.Category
import LeanW26.Categories.BinaryProduct
import LeanW26.Categories.Exponential

namespace LeanW26

open CategoryTheory

/-
Syntactic Categories
===

A `syntactic category` is a Category whose objects are types of expressions
and whose morphisms correspond to grammatical rules on the syntax.

For example, one might have a grammer of the form

```lean
   expr ::= const | var
   expr ::= -expr
   expr ::= expr + expr
```

To make a category for this bit of syntax, we would designate one object, 'expr' and four
morphisms for the const, var, negation and addition rules.

A `semantic` category is a category that provides the meaning of a syntax category
via a functor from the syntax to the semantics.
For example, we might have the category of natural numbers with additon and subtraction
as a semantic category for the above.

Regular Expressions
===

As a deeper example of a syntactic category, we will build the
category `RegExp` of regular expressions.

-/

inductive Alphabet : Type
| a : Alphabet
| b : Alphabet
| c : Alphabet

open Alphabet

inductive RegExp' : Type
| empty : RegExp'                       -- ∅
| epsilon : RegExp'                     -- ε
| char : Alphabet → RegExp'             -- single character
| alt : RegExp' → RegExp' → RegExp'     -- r₁ ∪ r₂
| seq : RegExp' → RegExp' → RegExp'     -- r₁r₂
| star : RegExp' → RegExp'              -- r*

--hide
open RegExp'
--unhide

/-
Here is an example of the regular expression `((a∪b)c)*` using the definitions above.

-/

def re1 : RegExp' := star (seq (alt (char a) (char b)) (char c))

/-
Acceptance
===

We will need to determine when two regular expressions correspond to the same set of strings.
To do that, we'll define the notion of acceptance for regular expressions as follows. -/

inductive accepts : RegExp' → List Alphabet → Prop
| epsilon : accepts epsilon []
| char : ∀ x : Alphabet, accepts (char x) [x]
| alt_left : ∀ r₁ r₂ s, accepts r₁ s → accepts (alt r₁ r₂) s
| alt_right : ∀ r₁ r₂ s, accepts r₂ s → accepts (alt r₁ r₂) s
| seq : ∀ r₁ r₂ s₁ s₂,
    accepts r₁ s₁ →
    accepts r₂ s₂ →
    accepts (seq r₁ r₂) (s₁ ++ s₂)
| star_nil : ∀ r, accepts (star r) []
| star_cons : ∀ r s₁ s₂,
    accepts r s₁ →
    accepts (star r) s₂ →
    accepts (star r) (s₁ ++ s₂)

/-
Example
===

We haven't really definied an algorithm for acceptance, as much as the logical
meaning of acceptance. So we can do proofs like the following, for example.
-/

example : accepts re1 [a, c, b, c] := by
  have : [a,c,b,c] = [a,c] ++ [b,c] := rfl
  rw[this]
  apply accepts.star_cons
  · have : [a,c] = [a] ++ [c] := rfl
    rw[this]
    apply accepts.seq
    · apply accepts.alt_left
      apply accepts.char
    apply accepts.char
  · have : [b,c] = [b,c] ++ [] := rfl
    rw[this]
    apply accepts.star_cons
    · have : [b,c] = [b] ++ [c] := rfl
      rw[this]
      apply accepts.seq
      · apply accepts.alt_right
        apply accepts.char
      apply accepts.char
    apply accepts.star_nil

/-
Example Theorem using Accepts
===

The notion of acceptance allows us to talk about regular expressions
by the set of strings the accept, as opposed to the syntax of the expression.
So, for example, here we show that the `alt` operator is commutative.
-/


theorem alt_comm {u v : RegExp'} {L : List Alphabet}
  : accepts (alt u v) L ↔ accepts u L ∨ accepts v L := by
  constructor
  · intro h
    cases h with
    | alt_left _ _ _ hu  => exact Or.inl hu
    | alt_right _ _ _ hv => exact Or.inr hv
  · intro h
    cases h with
    | inl h => apply accepts.alt_left; exact h
    | inr h => apply accepts.alt_right; exact h


/-
Equivalent Regular Expressions
===

We can now define an equivalence relation on regular expressions.

-/

def eq (re₁ re₂ : RegExp') : Prop := ∀ L, accepts re₁ L ↔ accepts re₂ L

theorem eq_refl (u : RegExp') : eq u u := by simp[eq]
theorem eq_symm {v w : RegExp'} : eq v w → eq w v := by simp_all[eq]
theorem eq_trans {u v w : RegExp'} : eq u v → eq v w → eq u w := by simp_all[eq]

instance eq_equiv : Equivalence eq := ⟨ eq_refl, eq_symm, eq_trans ⟩

@[simp]
instance regexp_has_equiv : HasEquiv RegExp' := ⟨ eq ⟩

/- These definitions set the stage for forming the quotient type for
RegExp'. They also let us write ≈ instead of `eq`: -/

#check eq re1 re1
#check re1 ≈ re1

/-
The Quotient
===

The thing that is actually a syntactic category is the quotient of `RegExp'` with respect
to `eq`, which we will call `RegExp`.

-/

instance regexp_setoid : Setoid RegExp' :=
  ⟨ eq, eq_equiv ⟩

def RegExp := Quotient regexp_setoid

def mk (w : RegExp') : RegExp := Quotient.mk regexp_setoid w

def RegExpCat := PUnit

instance inst_quiver : Quiver RegExpCat := ⟨
  fun _ _ => RegExp
⟩

/- Now we can write arrows between equivalence classes of regular expressions. -/

-- #check (mk re1) ⟶ (mk re1)

/-
The `seq` Operator
===

All of the operations respect equivalence. We will need a proof of one of them:
The `seq` operator respects equivalence. That is, if `w` and `y` are
equivalent and `x` and `z` are equivalent, then the equivalence classes
of `wx` and `yz` are equal.
-/

theorem seq_respects (w x y z : RegExp')
  : w ≈ y → x ≈ z → mk (RegExp'.seq w x) = mk (RegExp'.seq y z) := by
  intro h1 h2
  apply Quot.sound
  intro L
  constructor
  · intro h
    cases h with
    | seq _ _ s₁ s₂ hw hx =>
      apply accepts.seq
      · exact (h1 s₁).mp hw
      · exact (h2 s₂).mp hx
  · intro h
    cases h with
    | seq _ _ s₁ s₂ hw hx =>
      apply accepts.seq
      · exact (h1 s₁).mpr hw
      · exact (h2 s₂).mpr hx

/-
Lifted `seq`
===

With this theorem, we may use Lean's `Quotient.lift` to define `seq` on `RegExp`. -/

def seq_temp (x y : RegExp') : RegExp := mk (RegExp'.seq x y)
def RegExp.seq (x y : RegExp) : RegExp := Quotient.lift₂ seq_temp seq_respects x y

/- Now we can write ⟦w⟧ for the set of all expressions equivalent to w. We can show -/

example (u v : RegExp') : (⟦alt u v⟧ : RegExp) = ⟦alt v u⟧ := by
  apply Quot.sound
  simp[regexp_setoid,eq]
  intro L
  constructor
  repeat
  · intro h
    simp_all[alt_comm]
    exact id (Or.symm h)


/-
Identity and Composition
===

The Identity morphism for `RegExp` is `epsilon`:
-/

def regexp_id : RegExp := ⟦ RegExp'.epsilon ⟧

/- And composition is given by `seq`: -/

def reg_exp_comp (X Y Z : RegExpCat) (f : X ⟶ Y) (g : Y ⟶ Z) : RegExp := RegExp.seq f g

/-
Identity and Composition Theorems
===

We need theorems showing the identity composes on the left and right: -/

theorem id_comp {X Y : RegExpCat} (f : X ⟶ Y) : reg_exp_comp X X Y regexp_id f = f := by
    obtain ⟨ u, hu ⟩ := Quotient.exists_rep f
    rw[←hu]
    apply Quot.sound
    simp[regexp_setoid,eq]
    intro L
    constructor
    · intro h
      cases h with
      | seq _ _ s₁ s₂ hw hx =>
        cases hw
        exact hx
    · intro h
      have : L = [] ++ L := rfl
      rw[this]
      apply accepts.seq
      · apply accepts.epsilon
      exact h

theorem comp_id {X Y : RegExpCat} (f : X ⟶ Y) : reg_exp_comp X X Y f regexp_id = f := by
--brief
    obtain ⟨ u, hu ⟩ := Quotient.exists_rep f
    rw[←hu]
    apply Quot.sound
    intro L
    constructor
    · intro h
      cases h with
      | seq _ _ s₁ s₂ hw hx =>
        cases hx
        simp
        exact hw
    · intro h
      have : L = L ++ [] := Eq.symm (List.append_nil L)
      rw[this]
      apply accepts.seq
      ·  exact h
      exact accepts.epsilon
--unbrief

/-
The Associative Property of seq
===
-/

theorem assoc {W X Y Z : RegExpCat} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
  : reg_exp_comp W Y Z (reg_exp_comp W X Y f g) h =
    reg_exp_comp W X Z f (reg_exp_comp X Y Z g h) := by
    obtain ⟨ F, hF ⟩ := Quotient.exists_rep f
    obtain ⟨ G, hG ⟩ := Quotient.exists_rep g
    obtain ⟨ H, hH ⟩ := Quotient.exists_rep h
    rw[←hF,←hG,←hH]
    apply Quot.sound
    intro L
    constructor
    · intro h'
      cases h' with
      | seq _ _ s₁ s₂ hw hx =>
        cases hw with
        | seq _ _ s₃ s₄ hw' hx' =>
          have : s₃ ++ s₄ ++ s₂  = s₃ ++ (s₄ ++ s₂) := List.append_assoc s₃ s₄ s₂
          rw[this]
          apply accepts.seq
          · exact hw'
          exact accepts.seq G H s₄ s₂ hx' hx
    · intro h'
--brief
      cases h' with
      | seq _ _ s₁ s₂ hw hx =>
        cases hx with
        | seq _ _ s₃ s₄ hw' hx' =>
          have : s₁ ++ (s₃ ++ s₄) = s₁ ++ s₃ ++ s₄ :=  Eq.symm (List.append_assoc s₁ s₃ s₄)
          rw[this]
          apply accepts.seq
          · exact accepts.seq F G s₁ s₃ hw hw'
          exact hx'
--unbrief

/-
The Category Instance for RegExp
===
-/

instance : Category RegExpCat := {
  id (_ : RegExpCat ):= regexp_id,
  comp {X Y Z : RegExpCat} := reg_exp_comp X Y Z,
  id_comp {_ _ : RegExpCat} := id_comp,
  comp_id {_ _ : RegExpCat} := comp_id,
  assoc := assoc
}

--hide
end LeanW26
--unhide
