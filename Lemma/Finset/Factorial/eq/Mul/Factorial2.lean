import Mathlib.Data.Nat.Factorial.DoubleFactorial
import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  n ! = n ‼ * (n - 1) ‼ := by
-- proof
  cases n with
  | zero => rfl
  | succ m =>
    rw [Nat.factorial_eq_mul_doubleFactorial]
    simp


-- created on 2026-09-27
