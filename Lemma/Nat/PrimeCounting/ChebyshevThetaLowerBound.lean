import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.ChebyshevThetaLowerBound
open Real
open MetaMathlibExt


/--
[chebyshev_theta_gt_one_third](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ChebyshevThetaLowerBound.lean)
-/
@[path]
private lemma chebyshev_theta_gt_one_third_eq
  {x : ℝ}
-- given
  (hx : 3 ≤ x) :
-- imply
  x / 3 < Chebyshev.theta x := by
-- proof
  apply MetaMathlibExt.chebyshev_theta_gt_one_third x hx


-- created on 2026-10-20
