import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.ContractionDecay

section Shells

variable {G : Type*}

def shell (S : Set G) (φ : G → ℝ) (c r : ℝ) (k : ℕ) : Set G :=
  S ∩ φ ⁻¹' Ico (r ^ k * c) (r ^ (k + 1) * c)

end Shells

end MeasureTheory.ContractionDecay
