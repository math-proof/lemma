import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[tsum_interval_lengths](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ}
-- given
  (hε : 0 < ε) :
-- imply
  ∑' n : ℕ, (2 * ε / 2^(n+1)) = 2 * ε :=
-- proof
  tsum_interval_lengths ε hε


-- created on 2026-10-22
