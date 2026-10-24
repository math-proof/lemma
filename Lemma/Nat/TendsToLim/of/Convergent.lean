import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.lim_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
-- given
  (h: a.Convergent) :
-- imply
  a.TendsTo (lim a) :=
-- proof
  Chapter6.Sequence.lim_def h


-- created on 2026-10-22
