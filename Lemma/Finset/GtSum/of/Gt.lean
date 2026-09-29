import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f g : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, f i > g i) :
-- imply
  ∑ i ∈ Finset.range n, f i > ∑ i ∈ Finset.range n, g i := by
-- proof
  exact Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr h₀⟩ fun i _ => h i


-- created on 2026-09-27
