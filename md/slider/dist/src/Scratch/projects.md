


Bashir Abdel-Fattah
- Synthetic Differential Geometry

Alexandra Aiello
- SK

Dhruv Bhatia
- Resultants
- https://github.com/dhruvbhatia00/CPolynomial

Simon Chess
- CSLib

Harry Cui
- Signal processing

Adam Friesz
- Sequential Digital Systems
- https://github.com/frieszadam/formal-hdl

Luz Gomez
-- https://github.com/luzelenag123/EE598_Final_Project

Nat Hurtig
-- Machine Knitting
-- https://github.com/nhurtig/lean-category

Brian Ko
-- Backward Curriculum RL

Joe Leuschen
-- LIT
-- https://github.com/jleuschen17/LTI_Lean

Alex Lipson
-- HOTT?

Navya Mangipudi
-- FSMs / sequential logic

Nels Martin
-- RL
-- https://github.com/nelsmartin/RL-Dojo

Theodore Meek
-- Tactics for ML?

Anjali Pal
-- E-Graphs
-- https://github.com/ajpal/lean-egraph

Joeseph Rogge
-- https://github.com/joyjoie/LeanW26_Final ?

Jianxu Shangguan
-- Finite Automata

Sukhman Singh
-- Poly

Evan Wang
-- Verify Rust Linked List

Simon Wang
-- BFS
-- https://github.com/SimonW412/EE598_Final


Ryan Zambratta
-- https://github.com/rtzam/rincon



```lean
import Mathlib

--defines M as a 1D array of type float
abbrev M := Array Float

-- gives binary output based on the w ⬝ x + b part of the function
def h (x : Float) : Float :=
  if x > 0
  then 1
  else 0

def dot (w x : Array Float) : Float :=
  (List.range w.size).foldl (fun acc i => acc + w[i]! * x[i]!) 0.0

-- manually calculates a "dot product"
def f (w x : M) : Float := h (dot w x)

#eval f #[1,2] #[2,-3,2]

-- w is old weight vector, x is data, d is desired output (0 or 1),
-- output is new weight vector

def step (w x : M) (d r : Float) : M :=
  let change := r * (d - (f w x))
  w.mapIdx (fun i wi => wi + change * x[i]!)

-- iterates through each piece of data, updating the weights each time
def full_step (w : M) (data : List (M × Float)) : M :=
  data.foldl (fun wcur (row, label) => step wcur row label 0.25) w

--- TESTING ---

-- linearly separable data
def example_data : List (M × Float) := [
  (#[1, 2, 1], 1),
  (#[2, 1, 1], 0),
  (#[3, -1, 1], 0),
  (#[-3, 2, 1], 1),
  (#[-1, -2, 1], 0)
]

-- not linearly separable data
def example_data_2 : List (M × Float) := [
  (#[2, 3, 1], 0),
  (#[2, 2, 1], 1),
  (#[2, 1, 1], 0),
  (#[2, 0, 1], 1),
  (#[-2, -3, 1], 1),
  (#[-2, -2, 1], 0),
  (#[-2, -1, 1], 1),
  (#[-2, 0, 1], 1)
]

-- linearly separable calculations
def W0 := (#[0,0,2]:M)
def W1 := full_step W0 example_data
def W2 := full_step W1 example_data
def W3 := full_step W2 example_data
def W4 := full_step W3 example_data
#eval W1
#eval W2
#eval W3
#eval W4

#eval example_data.map (fun datum => f W1 datum.fst)
#eval example_data.map (fun datum => f W2 datum.fst)
#eval example_data.map (fun datum => f W3 datum.fst)
#eval example_data.map (fun datum => f W4 datum.fst)

-- not linearly separable calculations
def W0_2 := (#[0,0,2]:M)
def W1_2 := full_step W0_2 example_data_2
def W2_2 := full_step W1_2 example_data_2
def W3_2 := full_step W2_2 example_data_2
def W4_2 := full_step W3_2 example_data_2
#eval W1_2
#eval W2_2
#eval W3_2 -- converges here, why?
#eval W4_2


#eval example_data_2.map (fun datum => f W1_2 datum.fst)
#eval example_data_2.map (fun datum => f W2_2 datum.fst)
#eval example_data_2.map (fun datum => f W3_2 datum.fst)
#eval example_data_2.map (fun datum => f W4_2 datum.fst)
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

