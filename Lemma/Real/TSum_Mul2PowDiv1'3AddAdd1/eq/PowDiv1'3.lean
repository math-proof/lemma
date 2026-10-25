import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9


/--
[tsum_tail_bound](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {k : ℕ} :
-- imply
  ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(k + j + 1) = (1/3:ℝ)^k :=
-- proof
  tsum_tail_bound k


-- created on 2026-10-22
