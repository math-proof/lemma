import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Def.Analysis.Misc.UnitsSystem.Part7
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_in (d:Dimensions) (unit q:Scalar d) : unit.in q = q.val / unit.val := rfl

theorem Scalar.in_def {d:Dimensions} (unit q:Scalar d) [h: NeZero unit] : q = (unit.in q) • unit := by
  simp [neZero_iff] at h
  simp [←val_inj]
  field_simp

@[simp]
theorem Scalar.in_smul {d:Dimensions} (c:ℝ) (unit q:Scalar d) : unit.in (c • q) = c * unit.in q := by
  simp; ring

theorem Scalar.in_inj {d:Dimensions} (unit q₁ q₂:Scalar d) [h: NeZero unit] : unit.in q₁ = unit.in q₂ ↔ q₁ = q₂ := by
  simp [neZero_iff] at h
  simp [←val_inj]
  field_simp

end UnitsSystem
