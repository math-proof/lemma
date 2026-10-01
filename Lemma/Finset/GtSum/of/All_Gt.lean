import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i ∈ Finset.range n, f i > g i) :
-- imply
  ∑ i ∈ Finset.range n, f i > ∑ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr h₀⟩ h


-- created on 2019-01-22
