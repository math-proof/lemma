module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part7
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_smul {α} {d:Dimensions} [SMul α ℝ] (a : α) (q:Scalar d) : (a • q).val = a • q.val := rfl

end UnitsSystem
