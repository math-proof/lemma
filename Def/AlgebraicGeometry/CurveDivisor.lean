module

public import Mathlib.Data.Finsupp.Basic
public import Abbrev.AlgebraicGeometry.CurveDivisor

@[expose] public section

namespace CurveDivisor

variable {C : Type*}

/-- The coefficient of a point in a curve divisor. -/
def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

end CurveDivisor
