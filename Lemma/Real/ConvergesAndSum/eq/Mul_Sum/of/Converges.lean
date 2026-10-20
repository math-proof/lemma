import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_2
open Chapter7


/--
[smul](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {c:ℝ}
  {s:Series}
-- given
  (hs: s.converges) :
-- imply
  (c • s).converges ∧ (c • s).sum = c * s.sum :=
-- proof
  Chapter7.Series.smul hs


-- created on 2026-10-20
