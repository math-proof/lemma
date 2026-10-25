import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_6_1.Part17
open Chapter6
open Chapter6.Sequence


/--
[Sequence.boundedBy_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {M:ℝ} :
-- imply
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M :=
-- proof
  Chapter6.Sequence.boundedBy_def a M


-- created on 2026-10-22
