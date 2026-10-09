import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
open Continuant


@[path]
private lemma definition
  {x : ℕ → ℤ}
  {n : ℕ} :
-- imply
  H x (n + 2) = H x n + H x (n + 1) * x (n + 1) := by
-- proof
  rw [H]
  ring


-- created on 2021-07-30
