import Mathlib

namespace LeanW26

--notdone

/-
Todo
===

- Insert W25 lecture


- Sigma, PSigma, Exists

  Type    2nd Component  Universe   Proof Irrelevance Applies?
  ----------------------------------------------------------------
  Sigma   α → Type       Type       ❌ No
  PSigma  α → Prop       Type       ❌ No (not automatically)
  Exists  α → Prop       Prop       ✅ Yes

  When B x : Prop, the Pi type corresponds to universal quantification:
  ∀x:A,B(x)\forall x : A, B(x)∀x:A,B(x)
  When B x : Type, it’s a dependent function type:
  A function whose return type depends on the input.

  Sigma types are *not* required for expressibility. They are completely
  subsumed by inductive types. -/


def NatPos := Σ' n : Nat, n > 0

def x : NatPos := ⟨ 3 , by decide ⟩

#check NatPos -- Type
#check x -- NatPos, Not Prop

inductive NatPos2 (n : Nat) : Type
  | intro  : Π (_: n>0), NatPos2 n

def y : NatPos2 3 := ⟨ by decide ⟩
#check y -- NatPos, Not Prop

/-

Use of Sigma Types
  def NatPos := Σ n : Nat, n > 0
  def TypedValue := Σ T : Type, T
  def EvenNat := Σ n : Nat, n % 2 = 0
  def PreRat := Σ p : Int × Int, p.snd ≠ 0
  def TaggedValue (Tag : Type) := Σ t : Tag, String

All of these could be written inductively.



Todo
===

Pi types on the other hand are necessary to define dependent types and are
even used to define inductive types. For example,
-/

#check NatPos2.intro

/- is a Pi type. Lean doesn't write Pi out always, but it could have been written: -/

inductive NatPos3 (n : Nat) : Type
  | intro : Π (_: n>0), NatPos3 n

#check NatPos3.intro

def z : NatPos3 3 := ⟨ by decide ⟩
#check z -- NatPos, Not Prop



end LeanW26
