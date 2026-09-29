import sympy.sets.sets
import sympy.Basic
open Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  n * (n - 1) ! = n ! := by
-- proof
  exact Nat.mul_factorial_pred (by omega)


-- created on 2026-09-27
