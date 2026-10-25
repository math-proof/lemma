import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Def.Analysis.Misc.UnitsSystem.Part5
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_inv {d:Dimensions} (q:Scalar d) :
  q.inv.val = q.val⁻¹ := rfl

end UnitsSystem
