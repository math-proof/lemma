import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℤ → ℝ}
  {x : ℤ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (n.choose k : ℝ) * f (x + k) = Difference f n x := by
-- proof
  unfold Difference
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul]


-- created on 2021-11-26
