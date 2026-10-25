import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part19
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem StandardUnit.mul (d₁ d₂:Dimensions) : StandardUnit d₁ * StandardUnit d₂ = StandardUnit (d₁+d₂) := by
  simp [←Scalar.val_inj]

@[simp]
theorem StandardUnit.mul' (d₁ d₂:Dimensions) : (StandardUnit d₁:Formal) * (StandardUnit d₂:Formal) = StandardUnit (d₁+d₂) := by
  rw [←Scalar.toFormal_hMul, mul]

@[simp]
theorem StandardUnit.pow (d:Dimensions) (n:ℕ) : StandardUnit d ** n = StandardUnit (n • d) := by
  simp [←Scalar.val_inj]

@[simp]
theorem StandardUnit.pow' (d:Dimensions) (n:ℕ) : (StandardUnit d:Formal)^n = StandardUnit (n • d) := by
  rw [←Scalar.toFormal_pow, pow]

@[simp]
theorem StandardUnit.inv (d:Dimensions) : (StandardUnit d).inv = StandardUnit (-d) := by
  simp [←Scalar.val_inj]

@[simp]
theorem StandardUnit.div (d₁ d₂:Dimensions) : StandardUnit d₁ / StandardUnit d₂ = StandardUnit (d₁-d₂) := by
  simp [←Scalar.val_inj]

end UnitsSystem
