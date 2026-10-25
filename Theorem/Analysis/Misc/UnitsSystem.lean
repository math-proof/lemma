import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Structure.Analysis.Misc.UnitsSystem
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

theorem Scalar.val_injective (d : Dimensions) : Function.Injective (Scalar.val (d := d)) :=
  fun x y h => by aesop

/- One has the option to `work in coordinates` in a given calculation by using `simp [←val_inj]` (or `simp [←cast_eq]` below, if casting is required).  Or one can adopt
a `coordinate-free` approach in which any tool directly accessing `val` is avoided.
This library allows for both approaches to be employed. -/
theorem Scalar.val_inj {d:Dimensions} (q₁ q₂:Scalar d) :
  q₁.val = q₂.val ↔ q₁ = q₂ := Scalar.val_injective _ |>.eq_iff

end UnitsSystem
