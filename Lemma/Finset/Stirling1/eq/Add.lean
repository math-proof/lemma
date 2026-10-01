import Mathlib.Combinatorics.Enumerative.Stirling
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma recurrence
  {n k : ℕ} :
-- imply
  Nat.stirlingFirst (n + 1) (k + 1) = Nat.stirlingFirst n k + n * Nat.stirlingFirst n (k + 1) := by
-- proof
  rw [Nat.stirlingFirst_succ_succ]
  ring


-- created on 2026-09-27
