import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.isLUB_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real}
  {M: Chapter5.Real} :
-- imply
  IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M :=
-- proof
  Chapter5.Real.isLUB_def E M


-- created on 2026-10-22
