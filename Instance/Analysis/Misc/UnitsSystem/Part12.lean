import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part12
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- One can multiply a {lean}`Scalar d₁` and {lean}`Scalar d₂` quantities to obtain a {lean}`Scalar (d₁+d₂)` quantity,
in a manner compatible with multiplication in {name}`Formal`. -/
instance Scalar.instHMul {d₁ d₂:Dimensions} : HMul (Scalar d₁) (Scalar d₂) (Scalar (d₁ + d₂)) where
  hMul q₁ q₂ := ⟨q₁.val * q₂.val⟩

end UnitsSystem
