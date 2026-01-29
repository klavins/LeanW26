theorem x {p: Prop}: p ∨ ¬p := by grind

#print axioms x -- 'x' depends on axioms: [propext, Classical.choice, Quot.sound]
