module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part12
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_hMul {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  (q₁ * q₂).val = q₁.val * q₂.val := rfl

@[norm_cast,simp]
theorem Scalar.toFormal_hMul {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  ((q₁ * q₂:Scalar _):Formal) = (q₁:Formal) * (q₂:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]

end UnitsSystem
