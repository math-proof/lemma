import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_2
open Chapter7


/--
[converges_of_convergesTo](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s : Series}
  {L:ℝ}
-- given
  (h: s.convergesTo L) :
-- imply
  s.converges :=
-- proof
  Chapter7.Series.converges_of_convergesTo h


-- created on 2026-10-20
