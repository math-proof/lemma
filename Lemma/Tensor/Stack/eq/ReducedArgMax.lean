import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [NeZero n]
  {x : Fin m → Fin n → ℝ} :
-- imply
  (fun i => ArgMax Set.univ (x i)) = fun i => ArgMax Set.univ fun j => x i j :=
-- proof
  rfl


-- created on 2026-09-27
