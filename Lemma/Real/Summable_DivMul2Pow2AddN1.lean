import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[tsum_interval_summable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {ε : ℝ} :
-- imply
  Summable (fun n => 2 * ε / 2^(n+1) : ℕ → ℝ) :=
-- proof
  tsum_interval_summable ε


-- created on 2026-10-22
