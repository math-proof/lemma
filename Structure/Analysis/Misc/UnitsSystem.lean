import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Abbrev.Analysis.Misc.UnitsSystem
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- The data {name}`Scalar.val` of a {name}`Scalar` quantity can be interpreted as the numerical value of that
quantity with respect to some standard set of units (e.g., SI units). -/
@[ext]
structure Scalar (d:Dimensions) where
  val : ℝ

end UnitsSystem
