import Mathlib
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs
import Instance.Analysis.Misc.UnitsSystem
set_option doc.verso.suggestions false

attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


namespace UnitsSystem

variable [UnitsSystem]

/-- Many identities involving several types of {name}`Scalar`s can be dealt with by applying
{syntax tactic}`simp [←toFormal_inj]` to move everything to {name}`Formal`.  A large number of further {tactic}`simp` lemmas
in this file are then designed to simplify such {name}`Formal` expressions, often by pushing casting
operators inward back to the {name}`Scalar` types.  As such, there will be significant overlap between
the {tactic}`simp` and {tactic}`norm_cast` tags. -/
@[simp]
theorem Scalar.toFormal_inj {d: Dimensions} (q₁ q₂:Scalar d) :
  (q₁:Formal) = (q₂:Formal) ↔ q₁ = q₂ := by
  constructor
  · simp [toFormal, ←val_inj]
  intro h; simp [h]

/-- Conveniently, casts from one scalar to another will automatically disappear when moving to
{name}`Formal`. -/
@[simp]
theorem Scalar.toFormal_cast {d d': Dimensions} (q:Scalar d) (h:d' = d := by module) :
  ((q.cast h):Formal) = (q:Formal) := by
  subst h
  simp_all only [cast]

end UnitsSystem
