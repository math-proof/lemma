import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, f i < g i) :
-- imply
  ∑ i ∈ Finset.range n, f i < ∑ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) (fun i hi => h i (Finset.mem_range.mp hi))


-- created on 2019-01-30
