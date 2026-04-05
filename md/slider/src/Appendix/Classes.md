
<div class="lean-code" data-start-line="1" data-end-line="33"><pre><code>import Mathlib
import Lean

open Lean Elab Command

elab &quot;#class_parents &quot; n:ident : command =&gt; do
  let env ← getEnv
  let some info := getStructureInfo? env n.getId
    | logError m!&quot;{n.getId} is not a structure (or not found)&quot;; return
  -- Parents via `StructureInfo.parentInfo : Array StructureParentInfo`
  -- and `StructureParentInfo.structName : Name`.
  let ps : List Name := info.parentInfo.toList.map (·.structName)
  logInfo m!&quot;{n.getId} extends {String.intercalate &quot;, &quot; (ps.map (·.toString))}&quot;

#class_parents CommSemiring
  #class_parents Semiring
    #class_parents NonUnitalSemiring
      ...
    #class_parents NonAssocSemiring
      ...
    #class_parents MonoidWithZero
      ...
  #class_parents CommMonoid
#class_parents AddMonoidWithOne
  #class_parents NatCast
  #class_parents AddMonoid
    #class_parents AddSemigroup
      #class_parents Add
    #class_parents AddZeroClass
      #class_parents AddZero
        #class_parents Zero
        #class_parents Add
  #class_parents One</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

