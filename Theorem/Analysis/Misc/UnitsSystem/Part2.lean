import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Def.Analysis.Misc.UnitsSystem
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- This is a variant of {name}`Scalar.val_inj` that handles casts. -/
theorem Scalar.cast_eq {d d':Dimensions} (q: Scalar d) (q': Scalar d') (h: d = d' := by module)
  : q.val = q'.val ↔ q = q'.cast h := by aesop

theorem Scalar.cast_eq_symm {d d':Dimensions} (q: Scalar d) (q': Scalar d') (h: d = d' := by module)
  : q = q'.cast h ↔ q' = q.cast h.symm := by aesop

@[simp]
theorem Scalar.cast_val {d d':Dimensions} (q: Scalar d) (h: d' = d := by module)
  : (q.cast h).val = q.val := by aesop

end UnitsSystem
