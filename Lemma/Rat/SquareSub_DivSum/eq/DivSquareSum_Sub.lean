import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {y : ℝ}
-- given
  (h₀ : n > 0) :
-- imply
  (y - (∑ i ∈ Finset.range n, x i) / n) ^ 2 = (∑ i ∈ Finset.range n, (y - x i)) ^ 2 / n ^ 2 := by
-- proof
  have hn : (0 : ℝ) < n := by exact_mod_cast h₀
  have e : y - (∑ i ∈ Finset.range n, x i) / n = (∑ i ∈ Finset.range n, (y - x i)) / n := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [e, div_pow]


-- created on 2019-11-02
