import Lemma.Real.GtLog.of.Gt
import sympy.Basic
open Real


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hy : 0 < y)
  (h : x > y) :
-- imply
  Real.log x > Real.log y := by
-- proof
  apply GtLog.of.Gt hy h


-- created on 2026-10-17
