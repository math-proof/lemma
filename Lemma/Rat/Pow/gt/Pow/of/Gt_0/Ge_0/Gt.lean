import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[pow_gt_pow](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x y:ℚ}
  {n:ℕ}
-- given
  (hxy: x > y)
  (hy: y ≥ 0)
  (hn: n > 0) :
-- imply
  x^n > y^n :=
-- proof
  Section_4_3.pow_gt_pow x y n hxy hy hn


-- created on 2026-10-20
