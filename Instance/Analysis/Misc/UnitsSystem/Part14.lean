import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part16
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- Multiplication and inversion combine to give division in the usual fashion. -/
noncomputable instance Scalar.instHDiv {d₁ d₂:Dimensions} : HDiv (Scalar d₁) (Scalar d₂) (Scalar (d₁ - d₂)) where
  hDiv q₁ q₂ := ⟨q₁.val / q₂.val⟩

end UnitsSystem
