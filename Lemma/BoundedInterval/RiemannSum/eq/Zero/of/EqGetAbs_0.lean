import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval


/--
[riemann_sum_eq_zero_of_zero_length](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f : ℝ → ℝ}
  {I : BoundedInterval}
  {n : ℕ}
  {P : TaggedPartition I n}
-- given
  (h_len : |I|ₗ = 0) :
-- imply
  P.RiemannSum f = 0 :=
-- proof
  riemann_sum_eq_zero_of_zero_length h_len P


-- created on 2026-10-22
