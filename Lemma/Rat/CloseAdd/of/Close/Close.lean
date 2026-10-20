import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[close_trans](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {ε δ x y z:ℚ}
-- given
  (hxy: ε.Close x y)
  (hyz: δ.Close y z) :
-- imply
  (ε + δ).Close x z :=
-- proof
  Section_4_3.close_trans hxy hyz


-- created on 2026-10-20
