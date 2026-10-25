import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part10
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[norm_cast,simp]
theorem Formal.coe_zero : ((0:ℝ):Formal) = 0 := by
  simp

@[norm_cast,simp]
theorem Formal.coe_one : ((1:ℝ):Formal) = 1 := by
  rfl

@[norm_cast,simp]
theorem Formal.coe_nat (n:ℕ) : ((n:ℝ):Formal) = (n:Formal) := by
  rfl

@[norm_cast,simp]
theorem Formal.coe_int (n:ℤ) : ((n:ℝ):Formal) = (n:Formal) := by
  rfl

@[norm_cast,simp]
theorem Scalar.toFormal_smul {d:Dimensions} (c:ℝ) (q:Scalar d)
  : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem Formal.smul_eq_mul (c:ℝ) (x:Formal) : c • x = (c:Formal) * x := by
  ext n
  simp [Scalar.toFormal]

@[simp]
theorem Formal.smul_eq_mul' (c:ℕ) (x:Formal) : c • x = (c:Formal) * x := by
  simp

@[simp]
theorem Formal.smul_eq_mul'' (c:ℤ) (x:Formal) : c • x = (c:Formal) * x := by
  exact zsmul_eq_mul x c

@[norm_cast,simp]
theorem Scalar.coe_mul (r s:ℝ) : ((r*s:ℝ):Scalar 0) = r • (s:Scalar 0) := by
  ext; simp [ofReal]

end UnitsSystem
