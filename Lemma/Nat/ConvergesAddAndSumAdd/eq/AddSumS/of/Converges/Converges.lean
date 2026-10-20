import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_2
open Chapter7


/--
[add](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_2.lean)
-/
@[path]
private lemma main
  {s t:Series}
-- given
  (hs: s.converges)
  (ht: t.converges) :
-- imply
  (s + t).converges ∧ (s+t).sum = s.sum + t.sum :=
-- proof
  Chapter7.Series.add hs ht


-- created on 2026-10-20
