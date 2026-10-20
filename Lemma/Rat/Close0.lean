import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[close_refl](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x:ℚ} :
-- imply
  (0:ℚ).Close x x :=
-- proof
  Section_4_3.close_refl x


-- created on 2026-10-20
