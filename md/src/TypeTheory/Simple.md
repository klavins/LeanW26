
Type Universes
===

Arrow Types
===

```lean
#check (1,1)
#print Prod

-- Good explanation: https://www.youtube.com/watch?v=mTwvecBthpQ at 1:28:00

-- Simple : Just arrows, simple sums and products
-- But products are structures
#check fun x : Type => x
#check Type × Type
#check Type ⊕ Type
#check fun x : Type => (x,x)
#check fun x : Type => (Sum.inl x : Type ⊕ Type)

-- Inductive Types could go here

-- Polymorphic : Can have types as arguments or parameters
#check fun a : Type => fun x : a => x

-- Dependent : Can quantify over types
#check (x:Int) → x > 1
#check Π (x:Int), x > 1
#check ∀ (x:Int), x > 2
#check Σ (x:Nat), Fin (x+2)

-- Types on Types
def Option (α : Type) : Type := α ⊕ Unit



end LeanW26
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

