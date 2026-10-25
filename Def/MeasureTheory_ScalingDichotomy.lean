import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.ScalingDichotomy

section Slices

variable {G : Type*}

def zpowSlice (D : Set G) (f : G → ℝ) (r : ℝ) (k : ℤ) : Set G :=
  D ∩ f ⁻¹' Ico (r ^ k) (r ^ (k + 1))

end Slices

end MeasureTheory.ScalingDichotomy
