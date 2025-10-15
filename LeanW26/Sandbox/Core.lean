prelude

-- public section
-- set_option linter.missingDocs true -- keep it documented
-- @[expose] section  -- Expose all defs

#check Type
#check_failure 1
#check Sort

#check Prop

#check ∀ x : Prop, x

variable (A B : Type)
-- #check (A × (A → B)) → B

-- /- Note that X × Y is not really And, because it does not have type Prop.
--   -/
-- example : (A × (A → B)) → B := by
--   intro h
--   exact h.2 h.1

universe u v w

set_option linter.missingDocs false

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit

inductive True : Prop where
  | intro : True

inductive False : Prop

def Not (a : Prop) : Prop := a → False

-- structure And (a b : Prop) : Prop where
--   intro ::
--   left : a
--   right : b


structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

structure MProd (α β : Type u) where
  fst : α
  snd : β


set_option autoImplicit false


inductive And (p q : Prop) : Prop where
  | intro : p → q → (And p q)

def And.left {p q : Prop} (hpq : And p q) : p :=
  And.rec (fun hp _ => hp) hpq

def And.right {p q : Prop} (hpq : And p q) : q :=
  And.rec (fun _ hq => hq) hpq

example : Type 2 := Type 1

example (p : Prop) : Prop := p

example (p q : Prop) : (And p (p → q)) → q :=
  fun hpq => hpq.right hpq.left

-- example : ∀ x : A, A := sorry

example {f : A → Type} {b : Type} : Π x : A, A × A := by
  intro x
  exact (x,x)
