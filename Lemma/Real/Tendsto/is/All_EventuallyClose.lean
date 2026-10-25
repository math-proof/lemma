import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence

/--
[Sequence.tendsTo_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {L:ℝ} :
-- imply
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L :=
-- proof
  Chapter6.Sequence.tendsTo_def a L

-- created on 2026-10-22
