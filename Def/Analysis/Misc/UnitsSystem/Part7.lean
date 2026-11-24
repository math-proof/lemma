module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part22
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- {lean}`unit.in q` is {lean}`q : Scalar d` measured in terms of {lean}`unit : Scalar d`. -/
noncomputable def Scalar.in {d:Dimensions} (unit q:Scalar d) : ℝ := q.val / unit.val

end UnitsSystem
