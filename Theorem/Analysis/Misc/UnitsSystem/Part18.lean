import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part15
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_hDiv' {d:Dimensions} (q:Scalar d) (r:ℝ) :
  (q / r).val = q.val / r := rfl

@[simp]
theorem Scalar.val_hDiv'' {d:Dimensions} (q:Scalar d) (n:ℕ) :
  (q / n).val = q.val / n := rfl

@[simp]
theorem Scalar.val_hDiv''' {d:Dimensions} (q:Scalar d) (n:ℤ) :
  (q / n).val = q.val / n := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_hDiv' {d:Dimensions} (q:Scalar d) (r:ℝ) :
  ((q / r:Scalar _):Formal) = (q:Formal) * ((r⁻¹:ℝ):Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]
  congr

@[norm_cast,simp]
theorem Scalar.toFormal_hDiv'' {d:Dimensions} (q:Scalar d) (n:ℕ) :
  ((q / n:Scalar _):Formal) = (q:Formal) * (((n:ℝ)⁻¹:ℝ):Formal) := toFormal_hDiv' _ _

@[norm_cast,simp]
theorem Scalar.toFormal_hDiv''' {d:Dimensions} (q:Scalar d) (n:ℤ) :
  ((q / n:Scalar _):Formal) = (q:Formal) * (((n:ℝ)⁻¹:ℝ):Formal) := toFormal_hDiv' _ _

end UnitsSystem
