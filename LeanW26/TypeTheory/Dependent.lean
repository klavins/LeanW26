import Mathlib

namespace LeanW26

/-
Todo
===

    - Π x : T, M x
    - ∀ x : T, P x
    - Arrow types are actually a special case of dependent types
    - Gives you parametric polymoprhism

Todo
===
-/

/-
Sigma Types
===
-/

#print _root_.Sigma

structure Sigma.{u,v} {A : Type u} {B : A → Type v} where
  fst : A
  snd : B fst

def exampleSigma : Σ n : _root_.Nat, Fin n.succ :=
  ⟨3, ⟨2, by exact Nat.lt_of_sub_eq_succ rfl⟩⟩

def sig1 : @Sigma _root_.Nat (fun n => Fin (n+1)):=
  ⟨3, ⟨2, by exact Nat.lt_of_sub_eq_succ rfl⟩⟩

def sig2 : @Sigma _root_.Nat (fun n => Fin (n+1)):=
  ⟨3, ⟨2, by exact Nat.lt_of_sub_eq_succ rfl⟩⟩

def defaultValue : Σ α : Type, α := ⟨String, "default"⟩

def default : @Sigma Type (fun a => a)  := ⟨ String, "default" ⟩

-- A type-level function that is universe polymorphic
def Pair.{u, v} (α : Type u) (β : Type v) : Type (max u v) :=
  Prod α β

#check Pair Nat Bool          -- Type
#check List Nat
#check Pair (List Nat) Nat      -- Type 1



def Compose.{u, v, w}
    (F : Type v → Type w) (G : Type u → Type v) : Type u → Type w :=
  fun α => F (G α)

#check Compose Option List Nat  -- Option (List Nat)


def Arrow.{u, v} (α : Type u) (β : Type v) : Type (max u v) :=
  α → β

#check Arrow Nat Bool        -- Nat → Bool : Type
#check Arrow (List Nat) Nat    -- (Type 0) → Nat : Type 1


def Compose2.{u, v, w}
    (F : Type v → Type w) (G : Type u → Type v) : Type u → Type w :=
  fun α => F (G α)

#check Compose2 Option List Nat  -- Option (List Nat)

end LeanW26
