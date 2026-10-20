import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[le_abs](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ} :
-- imply
  -|x| ≤ x ∧ x ≤ |x| :=
-- proof
  Section_4_3.le_abs x


-- created on 2026-10-20
