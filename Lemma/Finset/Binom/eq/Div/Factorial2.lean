import Mathlib.Data.Nat.Factorial.DoubleFactorial
import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ((n * 2).choose n : ℚ) = (2 * n - 1) ‼ * 2 ^ n / n ! := by
-- proof
  have hf : ∀ m : ℕ, m ! = m ‼ * (m - 1) ‼ := by
    intro m
    cases m with
    | zero => rfl
    | succ k =>
      rw [Nat.factorial_eq_mul_doubleFactorial]
      simp
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n ≤ n * 2 by omega)
  rw [show n * 2 - n = n by omega, hf (n * 2), show n * 2 = 2 * n by ring, Nat.doubleFactorial_two_mul] at h1
  have key : (2 * n).choose n * n ! = (2 * n - 1) ‼ * 2 ^ n := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n)
    rw [h1]
    ring
  rw [eq_div_iff (by positivity), show n * 2 = 2 * n by ring]
  exact_mod_cast key


-- created on 2023-06-03
