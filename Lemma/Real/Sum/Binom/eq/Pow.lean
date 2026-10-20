import Mathlib.Data.Nat.Choose.Sum
import sympy.Basic


@[path]
private lemma main
  (r : ℕ)
  (x : ℝ) :
-- imply
  ∑ n ∈ Finset.range (r + 1), (r.choose n : ℝ) * x ^ n = (1 + x) ^ r := by
-- proof
  rw [show (1 + x) ^ r = (x + 1) ^ r by ring, add_pow]
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_comm]


-- created on 2021-11-25
-- updated on 2026-10-17
