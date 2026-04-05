
<div class="lean-code" data-start-line="1" data-end-line="18"><pre><code>import mathlib

#check Geometry.SimplicialComplex

#print AffineIndependent

def p : Geometry.SimplicialComplex ℤ ℤ := {
  faces := closure_of {{0,1,2},{1,2,4}},
  empty_notMem := by aesop,
  indep := sorry
  down_closed := by aesop
  inter_subset_convexHull {C1 C2} := by
    intro s t
    simp[convexHull,Convex,StarConvex]

    sorry

}</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

