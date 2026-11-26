import Mathlib.Algebra.Group.ForwardDiff
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  (Nat.factorial n : ℤ) = ∑ k < (n + 1), (-1) ^ (n - k) * (k : ℤ) ^ n * n.choose k := by
-- proof
  try simp only [Nat.Iio_eq_range] at *
  have e := fwdDiff_iter_eq_sum_shift (1 : ℤ) (fun r : ℤ => r ^ n) n 0
  rw [fwdDiff_iter_eq_factorial] at e
  simp only [Pi.natCast_apply, zero_add, smul_eq_mul, nsmul_eq_mul, mul_one] at e
  rw [e]
  exact Finset.sum_congr rfl (fun k _ => by ring)


-- created on 2020-10-13
