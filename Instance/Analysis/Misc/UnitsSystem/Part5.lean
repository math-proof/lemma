module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part6
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

instance Scalar.instNeZero_neg {d:Dimensions} (q:Scalar d) [h:NeZero q] : NeZero (-q) := by
  rw [neZero_iff] at h ⊢
  simp [h]

end UnitsSystem
