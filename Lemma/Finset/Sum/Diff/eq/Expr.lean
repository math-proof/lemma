import Mathlib.Algebra.Group.ForwardDiff
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {f : ℝ → ℝ}
  {x : ℝ} :
-- imply
  ∑ k < (n + 1), (n.choose k : ℝ) * (fwdDiff 1)^[k] f x = f (x + n) := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  have e := shift_eq_sum_fwdDiff_iter (1 : ℝ) f n x
  rw [nsmul_eq_mul, mul_one] at e
  rw [e]
  simp only [nsmul_eq_mul]


-- created on 2023-08-19
