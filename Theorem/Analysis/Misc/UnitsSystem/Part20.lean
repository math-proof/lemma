module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part17
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

theorem Scalar.val_lt {d:Dimensions} (x y:Scalar d) :
  x < y ↔ x.val < y.val := by simp only [lt_iff_not_ge, val_le]

end UnitsSystem
