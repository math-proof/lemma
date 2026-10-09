import Mathlib.Algebra.Group.ForwardDiff
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (k : ℤ) ^ n * n.choose k * (-1) ^ (n - k) = Nat.factorial n := by
-- proof
  have e := fwdDiff_iter_eq_sum_shift (1 : ℤ) (fun r : ℤ => r ^ n) n 0
  rw [fwdDiff_iter_eq_factorial] at e
  simp only [Pi.natCast_apply, zero_add, smul_eq_mul, nsmul_eq_mul, mul_one] at e
  rw [e]
  exact Finset.sum_congr rfl (fun k _ => by ring)


-- created on 2023-06-17
