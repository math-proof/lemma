import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Notation.Analysis.Misc.UnitsSystem
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_pow {d:Dimensions} (q:Scalar d) (n:ℕ) :
  (q ** n).val = q.val ^ n := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_pow {d:Dimensions} (q:Scalar d) (n:ℕ) :
  ((q ** n):Formal) = (q:Formal) ^ n := by
  simp [toFormal, AddMonoidAlgebra.single_pow]

end UnitsSystem
