import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[abs_eq_zero_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x: ℚ} :
-- imply
  |x| = 0 ↔ x = 0 :=
-- proof
  Section_4_3.abs_eq_zero_iff x


-- created on 2026-10-20
