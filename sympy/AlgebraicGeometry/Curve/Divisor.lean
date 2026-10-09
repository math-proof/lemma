import Mathlib.Data.Finsupp.Basic

/-!
# Divisors on a curve

This file defines divisors on an abstract type of points as formal finite integer linear
combinations of those points.
-/

/-- A divisor on a curve with point type `C` is a finitely supported integer-valued function on
`C`. Its support is available as `Finsupp.support`. -/
abbrev CurveDivisor (C : Type*) := C →₀ ℤ

namespace CurveDivisor

variable {C : Type*}

/-- The coefficient of a point in a curve divisor. -/
def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

@[simp]
theorem coeff_single (P : C) (n : ℤ) :
    coeff (Finsupp.single P n) P = n := by
  classical
  simp [coeff]

end CurveDivisor
