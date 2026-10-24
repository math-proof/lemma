import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[close_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {ε x y:ℚ} :
-- imply
  ε.Close x y ↔ |x - y| ≤ ε :=
-- proof
  Section_4_3.close_iff ε x y


-- created on 2026-10-22
