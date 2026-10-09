import Mathlib.Analysis.Real.Sqrt
import sympy.Basic


@[path]
private lemma main
  {x M : ℝ}
-- given
  (_hx : 0 < x)
  (h : x ≤ M) :
-- imply
  Real.sqrt x ≤ Real.sqrt M :=
-- proof
  Real.sqrt_le_sqrt h


-- created on 2019-08-13
