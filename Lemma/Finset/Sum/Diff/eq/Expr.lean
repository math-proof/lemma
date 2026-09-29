import Mathlib.Algebra.Group.ForwardDiff
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {f : ℝ → ℝ}
  {x : ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (fwdDiff 1)^[k] f x = f (x + n) := by
-- proof
  have e := shift_eq_sum_fwdDiff_iter (1 : ℝ) f n x
  rw [nsmul_eq_mul, mul_one] at e
  rw [e]
  simp only [nsmul_eq_mul]


-- created on 2026-09-27
