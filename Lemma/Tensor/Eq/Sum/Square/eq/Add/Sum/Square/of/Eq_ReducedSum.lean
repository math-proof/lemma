import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
  {xb t : ℝ}
-- given
  (h : xb = (∑ k ∈ Finset.range n, x k) / n) :
-- imply
  ∑ k ∈ Finset.range n, (x k - t) ^ 2 = n * (xb - t) ^ 2 + ∑ k ∈ Finset.range n, (x k - xb) ^ 2 := by
-- proof
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hS : ∑ k ∈ Finset.range n, x k = n * xb := by
    rw [h]
    field_simp
  have e : ∀ k ∈ Finset.range n, (x k - t) ^ 2 = (x k - xb) ^ 2 + 2 * (xb - t) * x k + (t ^ 2 - xb ^ 2) :=
    fun k _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hS, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  ring


-- created on 2023-11-06
