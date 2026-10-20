import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[add_close](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {ε δ x y z w:ℚ}
-- given
  (hxy: ε.Close x y)
  (hzw: δ.Close z w) :
-- imply
  (ε + δ).Close (x+z) (y+w) :=
-- proof
  Section_4_3.add_close hxy hzw


-- created on 2026-10-20
