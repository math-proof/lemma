import Mathlib.Data.Nat.Factorial.DoubleFactorial
import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  (n‼ : ℝ) = (n + 1)! / (n + 1)‼ := by
-- proof
  rw [eq_div_iff (by positivity), ← Nat.cast_mul, mul_comm, ← Nat.factorial_eq_mul_doubleFactorial]


@[main]
private lemma back
  {n : ℕ}
-- given
  (h : n ≥ 1) :
-- imply
  (n‼ : ℝ) = n ! / (n - 1)‼ := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, eq_div_iff (by positivity), ← Nat.cast_mul, ← Nat.factorial_eq_mul_doubleFactorial]


-- created on 2023-06-03
