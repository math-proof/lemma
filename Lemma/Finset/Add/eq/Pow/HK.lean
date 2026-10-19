import sympy.concrete.continuant
import sympy.sets.sets
open Continuant


@[path]
private lemma recurrence
  {x : ℕ → ℤ}
  {n : ℕ} :
-- imply
  H x (n + 1) * K x n - H x n * K x (n + 1) = (-1) ^ (n + 1) := by
-- proof
  induction n with
  | zero => simp [H, K]
  | succ n ih =>
    rw [H, K, pow_succ, ← ih]
    ring


-- created on 2020-08-14
