import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part13
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.mul_inv_self {d:Dimensions} (q:Scalar d) [h:NeZero q] : (q:Formal) * (q.inv:Formal) = 1 := by
  obtain ⟨ v ⟩ := q
  simp [neZero_iff] at h
  simp [inv, toFormal, AddMonoidAlgebra.single_mul_single,← Formal.coe_one]
  congr; field_simp

@[simp]
theorem Scalar.inv_mul_self {d:Dimensions} (q:Scalar d) [h:NeZero q] :  (q.inv:Formal) * (q:Formal) = 1 := by
  rw [mul_comm, mul_inv_self]

@[simp]
theorem Scalar.inv_coe (r:ℝ) :  ((r:Scalar 0).inv:Formal) = ((r⁻¹:ℝ):Scalar 0) := by
  rw [←toFormal_cast _ (show 0 = -0 by module)]; congr

@[simp]
theorem Scalar.mul_inv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) : (q₁ * q₂).inv = ((q₁.inv) * (q₂.inv)).cast := by
  ext
  simp [inv, val_hMul, cast_val, mul_inv_rev, mul_comm]

@[simp]
theorem Scalar.pow_inv {d:Dimensions} (q:Scalar d) (n:ℕ) : (q ** n).inv = (q.inv ** n).cast := by
  simp [←toFormal_inj, toFormal]

end UnitsSystem
