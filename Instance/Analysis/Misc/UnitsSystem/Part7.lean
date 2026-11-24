module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part8
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

instance Scalar.instSMul {α} {d:Dimensions} [SMul α ℝ] : SMul α (Scalar d) where
  smul c q := ⟨c • q.val⟩

end UnitsSystem
