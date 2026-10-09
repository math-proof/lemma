import sympy.Basic
import sympy.concrete.expr_with_limits


@[path]
private lemma main
  [NeZero n]
  {f : Fin m → Fin n → ℝ} :
-- imply
  (fun i => ArgMax Set.univ fun j => f i j) = fun i => ArgMax Set.univ (f i) :=
-- proof
  rfl


-- created on 2021-12-17
