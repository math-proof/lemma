import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} [NeZero n]
  {f : ℕ → ℝ} :
-- imply
  ArgMax (Set.univ : Set (Fin n)) (fun i => f i) = ArgMax Set.univ fun i : Fin n => f ↑i := by
-- proof
  rfl


-- created on 2023-11-05
