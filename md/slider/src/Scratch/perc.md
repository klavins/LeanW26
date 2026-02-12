

Todo

  Theory:
  - Show: If w*x = d then step w x = w

  Code
  - Change heaviside to f (because h is heaviside)
  - Remove dead code
  - Do 2D examples instead of 3D
     - Draw the points and the line you get

  Refactor
  - Try to rewrite code with arrays, lists or vectors to see if it
    can be fast
      - You might need to implement f as a for loop or similar
  - Try to use Float instead of ℚ and see if it is faster
      - Make an abbrev at top of file to easily switch

  Crazy long term goal:
  - Model pytorch as a DSL in Lean
  - Create proof infrastructure for reasoning about NNs expressed in DSL
  - Create a compile that takes NN model in Lean and outputs a Pytorch model




License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

