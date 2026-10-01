import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
-- given
  (_h : n > 0) :
-- imply
  n * (n - 1) * (n - 2) = n.choose 3 * Nat.factorial 3 := by
-- proof
  rw [mul_comm (n.choose 3), ← Nat.descFactorial_eq_factorial_mul_choose]
  simp [Nat.descFactorial_succ]
  ring


-- created on 2026-09-27
