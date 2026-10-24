/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinProjectiveDegree.lean -/


import sympy.atlas.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import Lemma.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0

import Mathlib.Tactic.Ring

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

/-- The three-coordinate primitivity criterion detects a constant coordinate. -/
example : PrimitiveTriple (X : ℚ[X]) (X + 1) 1 := by
  apply primitiveTriple_of_no_common_irreducible one_ne_zero
  intro p hp _ _ hpOne
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hpOne)

/-- The projective degree formula recovers the sum of numerator degrees. -/
example : (X ^ 2 : ℚ[X]).natDegree =
    (RatFunc.X : RatFunc ℚ).num.natDegree +
      (RatFunc.X : RatFunc ℚ).num.natDegree := by
  apply projective_first_natDegree (u := X ^ 2) (v := 2 * X) (h := 1)
  · exact ⟨0, 0, 1, by simp⟩
  · norm_num
  · exact RatFunc.X_ne_zero
  · exact RatFunc.X_ne_zero
  · simp only [map_pow, RatFunc.algebraMap_X, map_one, div_one]
    ring
  · simp only [map_mul, map_ofNat, RatFunc.algebraMap_X, map_one, div_one]
    ring

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
