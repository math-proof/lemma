import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[abs_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x: ℚ} :
-- imply
  |x| ≥ 0 :=
-- proof
  Section_4_3.abs_nonneg x


-- created on 2026-10-20
