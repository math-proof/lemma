import Mathlib.Analysis.Normed.Ring.InfiniteSum
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : ℕ → ℝ}
  {x : ℝ}
-- given
  (h₀ : Summable fun n => ‖A n * x ^ n‖)
  (h₁ : Summable fun n => ‖B n * x ^ n‖) :
-- imply
  (∑' n, A n * x ^ n) * (∑' n, B n * x ^ n) = ∑' n, (∑ k ∈ Finset.range (n + 1), A (n - k) * B k) * x ^ n := by
-- proof
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h₀ h₁]
  congr 1
  funext n
  rw [← Finset.sum_range_reflect, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega]
  rw [show x ^ n = x ^ (n - j) * x ^ j by rw [← pow_add, Nat.sub_add_cancel hj']]
  ring


-- created on 2026-09-27
