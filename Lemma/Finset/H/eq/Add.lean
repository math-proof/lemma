import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma definition
  {x : ℕ → ℤ}
  {n : ℕ} :
-- imply
  H x (n + 2) = H x n + H x (n + 1) * x (n + 1) := by
-- proof
  rw [H]
  ring


-- created on 2026-09-27
