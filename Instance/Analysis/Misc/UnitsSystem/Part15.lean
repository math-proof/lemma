import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Theorem.Analysis.Misc.UnitsSystem.Part17
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

noncomputable instance Scalar.instHDiv' {d:Dimensions} : HDiv (Scalar d) ℝ  (Scalar d) where
  hDiv q r := ⟨q.val / r⟩

noncomputable instance Scalar.instHDiv'' {d:Dimensions} : HDiv (Scalar d) ℕ (Scalar d) where
  hDiv q n := q / (n:ℝ)

noncomputable instance Scalar.instHDiv''' {d:Dimensions} : HDiv (Scalar d) ℤ (Scalar d) where
  hDiv q n := q / (n:ℝ)

end UnitsSystem
