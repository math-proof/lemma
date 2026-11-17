module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Class.Analysis.Misc.UnitsSystem
@[expose] public section

set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- The two key types here are {name}`Formal` and `Scalar d`.  `Scalar d` is the space of scalar
quantities whose units are given by `d : Dimensions`.  Collectively, they generate a graded commutative
 ring {name}`Formal`, which can be conveniently described using the existing Mathlib structure
 {name}`AddMonoidAlgebra`.  Algebraic manipulations of scalar quantities will be most conveniently
 handled by casting these quantities into the commutative ring {name}`Formal`, where one can use
 standard Mathlib tactics such as {name (full := Mathlib.Tactic.RingNF.ring)}`ring`.

In principle one could also develop vector-valued quantities with dimension, but for now we
restrict attention to scalar quantities only.
-/
abbrev Formal := AddMonoidAlgebra ℝ Dimensions

end UnitsSystem
