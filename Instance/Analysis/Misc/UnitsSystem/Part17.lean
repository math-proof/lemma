module
public import Mathlib
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Algebra.Order.Module.Defs
public import Theorem.Analysis.Misc.UnitsSystem.Part19
set_option doc.verso.suggestions false


public section

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

noncomputable instance Scalar.instLinearOrder (d:Dimensions) : LinearOrder (Scalar d) where
  le_refl := by simp [val_le]
  le_trans := by simp [val_le]; intros; order
  lt_iff_le_not_ge := by simp [val_le]
  le_antisymm := by simp [val_le, ←val_inj]; intros; order
  le_total := by simp [val_le]; intros; apply LinearOrder.le_total
  toDecidableLE := Classical.decRel _

end UnitsSystem
