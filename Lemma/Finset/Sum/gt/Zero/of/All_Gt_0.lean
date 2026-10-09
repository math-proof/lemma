import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, f i > 0) :
-- imply
  ∑ i ∈ Finset.range n, f i > 0 := by
-- proof
  exact Finset.sum_pos (fun i hi => h i (Finset.mem_range.mp hi)) (Finset.nonempty_range_iff.mpr (by omega))


-- created on 2019-01-23
