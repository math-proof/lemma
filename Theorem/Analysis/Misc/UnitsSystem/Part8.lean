module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Instance.Analysis.Misc.UnitsSystem.Part6
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_sub {d:Dimensions} (q₁ q₂ : Scalar d) : (q₁ - q₂).val = q₁.val - q₂.val := rfl

@[simp,norm_cast]
theorem Scalar.toFormal_sub {d:Dimensions} (q₁ q₂ :Scalar d) : ((q₁ - q₂ :Scalar d):Formal) = (q₁:Formal) - q₂ := by
  simp [toFormal, val_sub]

end UnitsSystem
