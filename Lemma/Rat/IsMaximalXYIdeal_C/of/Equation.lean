import Mathlib
import sympy.Basic

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

/--
[WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal.lean)
-/
@[main]
private lemma main
  [Field K]
  {W : Affine K}
  {a b : K}
-- given
  (h : W.Equation a b) :
-- imply
  (XYIdeal W a (C b)).IsMaximal :=
-- proof
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField K) (quotientXYIdealEquiv (W' := W) h).toMulEquiv


-- created on 2026-10-03
