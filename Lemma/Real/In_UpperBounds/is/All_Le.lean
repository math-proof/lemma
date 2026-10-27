import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.upperBound_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
  {M: Chapter5.Real} :
-- imply
  M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
-- proof
  Chapter5.Real.upperBound_def E M


-- created on 2026-10-22
