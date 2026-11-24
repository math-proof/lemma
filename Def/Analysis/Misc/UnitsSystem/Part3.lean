module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part8
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- The dimensionless scalars {lean}`Scalar 0` can be identified with real numbers.  -/
@[coe]
def Scalar.ofReal (r:ℝ) : Scalar 0 := ⟨ r ⟩

end UnitsSystem
