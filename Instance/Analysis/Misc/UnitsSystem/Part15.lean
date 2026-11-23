module

public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part17
@[expose] public section

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
