import sympy.core.function
import sympy.Basic


@[path]
private lemma main
  {n d : ℕ}
  {δ : ℝ}
-- given
  (h : d < n) :
-- imply
  Difference (fun x : ℝ => (x + δ) ^ d) n = 0 := by
-- proof
  funext x
  unfold Difference
  rw [fwdDiff_iter_comp_add 1 (fun r : ℝ => r ^ d) δ n x, fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl


-- created on 2021-12-01
