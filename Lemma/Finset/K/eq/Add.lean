import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma definition
  {x : ℕ → ℤ}
  {n : ℕ} :
-- imply
  K x (n + 2) = K x n + K x (n + 1) * x (n + 1) := by
-- proof
  rw [K]
  ring


-- created on 2026-09-27
