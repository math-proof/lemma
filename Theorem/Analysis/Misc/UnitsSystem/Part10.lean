import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part9
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.coe_val (r:ℝ) : (r:Scalar 0).val = r := rfl

@[norm_cast,simp]
theorem Scalar.coe_zero : ((0:ℝ):Scalar 0) = 0 := rfl

theorem Scalar.neZero_coe_iff {r:ℝ} : NeZero (r:Scalar 0) ↔ r ≠ 0 := by
  simp [neZero_iff]

@[simp]
theorem Scalar.coe_inj {r s:ℝ} : (r:Scalar 0) = (s:Scalar 0) ↔ r = s := by
  simp [ofReal]

@[norm_cast,simp]
theorem Scalar.coe_add (r s:ℝ) : ((r+s:ℝ):Scalar 0) = (r:Scalar 0) + (s:Scalar 0) := rfl

@[norm_cast,simp]
theorem Scalar.coe_neg (r:ℝ) : ((-r:ℝ):Scalar 0) = -(r:Scalar 0) := rfl

@[norm_cast,simp]
theorem Scalar.coe_sub (r s:ℝ) : ((r-s:ℝ):Scalar 0) = (r:Scalar 0) - (s:Scalar 0) := by
  simp [ofReal]; rfl

end UnitsSystem
