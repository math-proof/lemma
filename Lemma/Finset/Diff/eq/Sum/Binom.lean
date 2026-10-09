import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℝ → ℝ}
  {x : ℝ} :
-- imply
  Difference f n x = ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (n.choose k : ℝ) * f (x + k) := by
-- proof
  unfold Difference
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]


-- created on 2020-10-10
