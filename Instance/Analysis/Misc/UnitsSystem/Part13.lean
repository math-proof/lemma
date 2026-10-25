import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part15
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

instance Scalar.instNeg_inv {d:Dimensions} (q:Scalar d) [h: NeZero q] : NeZero q.inv := by
  rw [neZero_iff] at h ⊢
  simp [h]

end UnitsSystem
