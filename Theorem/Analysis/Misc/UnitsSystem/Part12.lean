import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part11
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_smul' {d:Dimensions} (c:ℕ) (q:Scalar d) : (c • q).val = c * q.val := by simp [←Nat.cast_smul_eq_nsmul ℝ]

@[simp]
theorem Scalar.val_smul'' {d:Dimensions} (c:ℤ) (q:Scalar d) : (c • q).val = c * q.val := by simp [←Int.cast_smul_eq_zsmul ℝ]

@[norm_cast,simp]
theorem Scalar.toFormal_smul' {d:Dimensions} (c:ℕ) (q:Scalar d)
  : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [←Nat.cast_smul_eq_nsmul ℝ]

@[norm_cast,simp]
theorem Scalar.toFormal_smul'' {d:Dimensions} (c:ℤ) (q:Scalar d)
  : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [←Int.cast_smul_eq_zsmul ℝ]

end UnitsSystem
