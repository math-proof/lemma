import sympy.functions.combinatorial.numbers
import sympy.Basic


@[path]
private lemma recurrence
  {n k : ℕ} :
-- imply
  Stirling (n + 1) (k + 1) = Stirling n k + (k + 1) * Stirling n (k + 1) := by
-- proof
  unfold Stirling
  rw [Nat.stirlingSecond_succ_succ, add_comm]


-- created on 2026-09-27
