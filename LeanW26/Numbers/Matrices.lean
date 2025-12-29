/-

  Pi types inherit zero, one, addition, subtraction, etc.

  instance (ι : Type) (β : ι → Type) [∀ i, Add (β i)] : Add (∀ i, β i)

  This works with fully reducible types like

abbrev Tensor : Shape → Type
  | [] => ℝ
  | k :: s' => Fin k → Tensor s'

open Tensor

#synth Zero (Tensor [1,2])
#synth One (Tensor [1,2])
#synth Add (Tensor [1,2])
#synth Sub (Tensor [1,2])
#synth Neg (Tensor [1,2])
#synth Mul (Tensor [1,2])
#synth SMul ℝ (Tensor [1,2])

-/
