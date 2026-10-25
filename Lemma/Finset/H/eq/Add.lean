import Def.Algebra.ContinuedFractions.Continuant
import sympy.sets.sets
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
