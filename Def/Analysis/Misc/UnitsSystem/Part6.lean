module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part18
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

-- TODO: add in some `gcongr` lemmas for this order

/-- The standard unit of {lean}`Scalar d` is the quantity whose data {name}`Scalar.val` is equal to {lean (type := "ℝ")}`1`. -/
def StandardUnit (d:Dimensions) : Scalar d := ⟨ 1 ⟩

end UnitsSystem
