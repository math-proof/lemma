import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[close_mul_right](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {ε x y z:ℚ}
-- given
  (hxy: ε.Close x y) :
-- imply
  (ε*|z|).Close (x * z) (y * z) :=
-- proof
  Section_4_3.close_mul_right hxy


-- created on 2026-10-20
