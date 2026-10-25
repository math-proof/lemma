/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/Curve/Divisor.lean -/

import Mathlib.Data.Finsupp.Basic


/-!
# Divisors on a curve

This file defines divisors on an abstract type of points as formal finite integer linear
combinations of those points.
-/

/-- A divisor on a curve with point type `C` is a finitely supported integer-valued function on
`C`. Its support is available as `Finsupp.support`. -/
abbrev CurveDivisor (C : Type*) := C →₀ ℤ

