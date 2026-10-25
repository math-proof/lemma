import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_3.Part2
open Section_4_3


/--
[close_mul_mul](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {ε δ x y z w:ℚ}
-- given
  (hxy: ε.Close x y)
  (hzw: δ.Close z w) :
-- imply
  (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) :=
-- proof
  Section_4_3.close_mul_mul hxy hzw


-- created on 2026-10-20
