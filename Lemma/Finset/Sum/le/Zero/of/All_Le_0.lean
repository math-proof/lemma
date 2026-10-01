import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h : ∀ i < n, f i ≤ 0) :
-- imply
  ∑ i ∈ Finset.range n, f i ≤ 0 := by
-- proof
  exact Finset.sum_nonpos (fun i hi => h i (Finset.mem_range.mp hi))


-- created on 2019-01-27
