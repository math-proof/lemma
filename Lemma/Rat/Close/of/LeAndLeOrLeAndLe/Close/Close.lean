import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_3
open Section_4_3


/--
[close_between](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {ε x y z w:ℚ}
-- given
  (hxy: ε.Close x y)
  (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) :
-- imply
  ε.Close x w :=
-- proof
  Section_4_3.close_between hxy hxz hbetween


-- created on 2026-10-20
