import Mathlib.Data.Nat.Choose.Sum
import sympy.Basic


@[path]
private lemma main
  (r : ℕ)
  (x : ℝ) :
-- imply
  ∑ n ∈ Finset.range (r + 1), (n : ℝ) * (r.choose n : ℝ) * x ^ n =
    (r : ℝ) * x * (1 + x) ^ (r - 1) := by
-- proof
  cases r with
  | zero =>
    simp
  | succ r =>
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel]
    have hpow : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * x ^ k = (1 + x) ^ r := by
      rw [show (1 + x) ^ r = (x + 1) ^ r by ring, add_pow]
      apply Finset.sum_congr rfl
      intro n hn
      simp [mul_comm]
    calc
      _ = ∑ k ∈ Finset.range (r + 1), (r + 1 : ℝ) * (r.choose k : ℝ) * x ^ (k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hnat : (k + 1) * (r + 1).choose (k + 1) = (r + 1) * r.choose k := by
          rw [mul_comm]
          exact (Nat.add_one_mul_choose_eq r k).symm
        rw [show ((k + 1 : ℕ) : ℝ) * ((r + 1).choose (k + 1) : ℝ) =
          (r + 1 : ℝ) * (r.choose k : ℝ) by exact_mod_cast hnat]
      _ = (r + 1 : ℝ) * x * ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * x ^ k := by
        have hterm (k : ℕ) : (r + 1 : ℝ) * (r.choose k : ℝ) * x ^ (k + 1) = (r + 1 : ℝ) * x * ((r.choose k : ℝ) * x ^ k) := by
          rw [pow_succ]
          ring
        simp_rw [hterm, ← Finset.mul_sum]
      _ = (↑(r + 1) : ℝ) * x * (1 + x) ^ r := by
        rw [hpow]
        norm_cast


-- created on 2021-11-25
-- updated on 2026-10-17
