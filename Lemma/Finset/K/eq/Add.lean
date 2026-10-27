import Def.Algebra.ContinuedFractions.Continuant
import Theorem.Data.Set.Sets
open Continuant


@[path]
private lemma definition
  {x : ℕ → ℤ}
  {n : ℕ} :
-- imply
  K x (n + 2) = K x n + K x (n + 1) * x (n + 1) := by
-- proof
  rw [K]
  ring


-- created on 2021-08-18
