import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem.Part2
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

@[simp]
theorem Scalar.val_zero {d:Dimensions} : (0:Scalar d).val = 0 := rfl

/-- We will use the {name}`NeZero` class to tag some scalars as non-zero; this becomes relevant when
using such scalars as units.  One could also introduce API to tag some scalars as positive, but
we currently are not implementing this. -/
theorem Scalar.neZero_iff {d:Dimensions} (q:Scalar d) : NeZero q ↔ q.val ≠ 0 := by simp [_root_.neZero_iff, ←val_inj]

@[simp, norm_cast]
theorem Scalar.toFormal_zero {d:Dimensions} : ((0:Scalar d):Formal) = 0 := by
  simp only [toFormal, AddMonoidAlgebra.single, val_zero, Finsupp.single_zero]
  rfl

end UnitsSystem
