module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part3
@[expose] public section

set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

instance Scalar.instZero {d:Dimensions} : Zero (Scalar d) where
  zero := ⟨ 0 ⟩

end UnitsSystem
