/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Divisor.lean -/

import Mathlib.Data.Finsupp.Basic
import Abbrev.AlgebraicGeometry.Curve.Divisor


namespace CurveDivisor

variable {C : Type*}

/-- The coefficient of a point in a curve divisor. -/
def coeff (D : CurveDivisor C) (P : C) : ℤ := D P

end CurveDivisor
