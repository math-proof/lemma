import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_7_2.Part5
open Chapter7


/--
[convergesTo_sum](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s : Series}
-- given
  (h: s.converges) :
-- imply
  s.convergesTo s.sum :=
-- proof
  Chapter7.Series.convergesTo_sum h


-- created on 2026-10-20
