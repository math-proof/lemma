import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part7
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

instance Scalar.instSub {d:Dimensions} : Sub (Scalar d) where
  sub q₁ q₂ := ⟨q₁.val - q₂.val⟩

end UnitsSystem
