- Affine form: w · x + b. 
```lean
def affine {n : Nat} (w x : Vector Float n) (b : Float) : Float :=
  dot w x + b


#eval 3 • w

-- -- gives binary output based on the w ⬝ x + b part of the function
-- def h (x : M 1 1) : ℚ :=
--   if x 0 0 > 0 -- 0 0 means 0th row, 0th column
--   then 1
--   else 0

-- -- defines the whole Heaviside function
-- -- def f {n : ℕ} (w x : Matrix (Fin 1) (Fin n) ℚ) (b : ℚ) : M 1 1 :=
-- --   !![ h (w * x.transpose + !![b]) ]

-- -- #eval f w x 4 -- testing function
-- -- #eval f w (-x) 4

-- -- #check f (f w x 4) (f w x 4) 5 -- nesting the Heaviside function (multiple steps)

-- def w2 : M 1 5 := !![0.4, 2.3, 9.7, 3.4, 4] -- includes b as the last number (4)
-- def x2 : M 1 5 := !![0.4, 2.3, 9.7, 3.4, 1] -- last number always 1

-- -- #eval f w2 x2 0

-- -- swallow b as last number in w, and make last number in x be 1
-- def heaviside {n : ℕ} (w x : Matrix (Fin 1) (Fin n) ℚ) : ℚ :=
--   h (w * x.transpose)

-- #eval heaviside w2 x2
-- #check heaviside w2 x2
-- #eval (2:ℚ)•w2
-- -- • is made with \smul

-- def step {n : ℕ} (w x : M 1 n) (d : Fin 2) (r : ℚ) : M 1 n :=
--   w + r • (d - (heaviside w x)) • x
--   -- w is old weight vector
--   -- x is data
--   -- d is desired output (0 or 1)
--   -- output is new weight vector
-- #eval step w2 x2 0 0.5

-- def full_step {n : ℕ} (w : M 1 n) (data : List (M 1 n × Fin 2)) : M 1 n :=
--   data.foldl (fun wcur (row, label) => step wcur row label 0.5) w

-- -- linearly separable data
-- def example_data : List (M 1 4 × Fin 2) := {
--   (!![0, 1, 2, 1], 0),
--   (!![2, 1, 2, 1], 1),
--   (!![0, -1, 1, 1], 1)
-- }

-- -- -- not linearly separable data
-- -- def example_data_2 : List (M 1 4 × Fin 2) := {
-- --   (!![0.4, -3, 0.2, 1], 0),
-- --   (!![0.4, -3, 0.2, 1], 1),
-- --   (!![0.4, -30, 3.4, 1], 1),
-- --   (!![0.4, -30, 3.4, 1], 0)
-- -- }

-- -- linearly separable calculations - converges immediately
-- def W0 := (!![0,0,0,2]:M 1 4)
-- def W1 := full_step W0 example_data
-- def W2 := full_step W1 example_data
-- def W3 := full_step W2 example_data

-- #eval W1
-- #eval W2

-- #eval example_data[0].fst

-- def ed0 := (example_data[0].fst : Matrix (Fin 1) (Fin 4) ℚ)
-- def ed1 := (example_data[1].1 : Matrix (Fin 1) (Fin 4) ℚ)
-- def ed2 := (example_data[2].1 : Matrix (Fin 1) (Fin 4) ℚ)

-- #check heaviside

-- #eval heaviside W0 ed0
-- #eval heaviside W0 ed1
-- #eval heaviside W0 ed2

-- #eval heaviside W2 ed0
-- #eval heaviside W2 ed1
-- #eval heaviside W2 ed2

-- #eval W3


-- -- -- not linearly separable calculations - does not converge
-- -- def W0_2 := (!![0,0,0,2]:M 1 4)
-- -- def W1_2 := full_step W0_2 example_data_2
-- -- def W2_2 := full_step W1_2 example_data_2
-- -- def W3_2 := full_step W2_2 example_data_2
-- -- #eval W1_2
-- -- #eval W2_2
-- -- #eval W3_2 -- why doesn't this one load?
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

