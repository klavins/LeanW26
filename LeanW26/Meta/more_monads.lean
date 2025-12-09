
import LeanW26.Meta.monads

namespace LeanW26.Monads

/-
Getting Inside a Monad
===

The `<$>` is a way to apply a function to the value inside a Monad. -/

#eval (λ x => x+1) <$> Maybe.some 1

/- It doesn't do anything to `none`. -/

#eval (λ x => x+1) <$> Maybe.none




/- Maybe satisfies all the monad rules. -/

instance : LawfulFunctor Maybe :=
 ⟨ by -- Functor.mapConst = Functor.map ∘ Function.const β -- how is this about Maybe?
     exact fun {α β} ↦ rfl,
   by -- id <$> x = x
     intro α m
     rcases m <;> rfl,
   by -- (h ∘ g) <$> x = h <$> g <$> x
     intro a b c g h m
     rcases m <;> rfl
   ⟩

instance : LawfulApplicative Maybe :=
  ⟨ by -- x <* y = Function.const β <$> x <*> y
      intro a b m n
      rcases m <;> rfl,
    by -- x *> y = Function.const α id <$> x <*> y
      intro a b m n
      rcases m <;> rcases n <;> rfl,
    by -- pure g <*> x = g <$> x
      intro a b g m
      rcases m <;> rfl,
    by -- g <$> pure x = pure (g x)
      intro a b g x
      rfl,
    by -- g <*> pure x = (fun h ↦ h x) <$> g
      intro a b g x
      rfl,
    by -- h <*> (g <*> x) = Function.comp <$> h <*> g <*> x
      intro a b c m n p
      rcases m <;> rcases n <;> rcases p <;> rfl
     ⟩

instance : LawfulMonad Maybe :=
  ⟨
    by -- (do; let a ← x;  pure (f a)) = f <$> x
      intro a b f m
      rcases m <;> rfl,
    by -- (do; let x_1 ← f; x_1 <$> x) = f <*> x
      intro a b m n
      rcases m <;> rcases n <;> rfl,
    by -- pure x >>= f = f x
      intro a b x f
      have m := f x
      rcases m <;> rfl,
    by -- x >>= f >>= g = x >>= fun x ↦ f x >>= g
      intro a b c m n p
      rcases m <;> rfl
  ⟩

end LeanW26.Monads
