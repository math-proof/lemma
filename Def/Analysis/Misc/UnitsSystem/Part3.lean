import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part8
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- The dimensionless scalars {lean}`Scalar 0` can be identified with real numbers.  -/
@[coe]
def Scalar.ofReal (r:ℝ) : Scalar 0 := ⟨ r ⟩

end UnitsSystem
