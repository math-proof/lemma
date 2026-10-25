import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_4_3.Part2
open Section_4_3 hiding abs dist


/--
[abs_of_pos](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_3.lean)
-/
@[path]
private lemma main
  {x: ℚ}
-- given
  (hx: 0 < x) :
-- imply
  Section_4_3.abs x = x :=
-- proof
  Section_4_3.abs_of_pos hx


-- created on 2026-10-22
