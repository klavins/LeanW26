import Mathlib
import Lean

open Lean Elab Command

elab "#class_parents " n:ident : command => do
  let env ← getEnv
  let some info := getStructureInfo? env n.getId
    | logError m!"{n.getId} is not a structure (or not found)"; return
  -- Parents via `StructureInfo.parentInfo : Array StructureParentInfo`
  -- and `StructureParentInfo.structName : Name`.
  let ps : List Name := info.parentInfo.toList.map (·.structName)
  logInfo m!"{n.getId} extends {String.intercalate ", " (ps.map (·.toString))}"

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
  #class_parents One
