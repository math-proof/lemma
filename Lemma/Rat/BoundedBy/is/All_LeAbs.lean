import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_1
open Chapter5


/--
[boundedBy_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  {a:Sequence}
  {M:ℚ} :
-- imply
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M :=
-- proof
  Chapter5.Sequence.boundedBy_def a M


-- created on 2026-10-20
