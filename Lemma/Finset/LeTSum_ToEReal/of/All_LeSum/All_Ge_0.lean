import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open EReal


/--
[EReal.tsum_le_of_sum_range_le](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {f : ℕ → ℝ}
  {c : EReal}
-- given
  (hf : ∀ n, 0 ≤ f n)
  (h : ∀ N, (∑ i ∈ Finset.range N, f i : EReal) ≤ c) :
-- imply
  ∑' n, (f n).toEReal ≤ c :=
-- proof
  EReal.tsum_le_of_sum_range_le hf h


-- created on 2026-10-22
