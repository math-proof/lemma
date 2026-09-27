import Mathlib.Algebra.Order.Group.Nat
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
-- given
  (h₀ : 0 < m)
  (n : ℕ) :
-- imply
  (m - 1) * n + n = m * n := by
-- proof
  rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left n h₀)]


-- created on 2026-09-26
