import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[abs_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x y:ℚ} :
-- imply
  |x + y| ≤ |x| + |y| :=
-- proof
  Section_4_3.abs_add x y


-- created on 2026-10-20
