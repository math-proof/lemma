import Mathlib.Algebra.Group.ForwardDiff
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (k : ℤ) ^ n * n.choose k = Nat.factorial n * (-1) ^ n := by
-- proof
  have e := fwdDiff_iter_eq_sum_shift (1 : ℤ) (fun r : ℤ => r ^ n) n 0
  rw [fwdDiff_iter_eq_factorial] at e
  simp only [Pi.natCast_apply, zero_add, smul_eq_mul, nsmul_eq_mul, mul_one] at e
  rw [e, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hp : (-1 : ℤ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : ((-1 : ℤ) ^ (n - k)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hp]
  linear_combination (-((-1 : ℤ) ^ k * (k : ℤ) ^ n * (n.choose k : ℤ))) * h2


-- created on 2026-09-27
