module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part5
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp,norm_cast]
theorem Scalar.toFormal_neg {d:Dimensions} (q:Scalar d) : ((-q:Scalar d):Formal) = -(q:Formal) := by
  simp [toFormal, val_neg]

end UnitsSystem
