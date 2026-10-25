import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.tendsTo_unique](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {L L':ℝ}
-- given
  (h:L ≠ L') :
-- imply
  ¬ (a.TendsTo L ∧ a.TendsTo L') :=
-- proof
  Chapter6.Sequence.tendsTo_unique a h


-- created on 2026-10-22
