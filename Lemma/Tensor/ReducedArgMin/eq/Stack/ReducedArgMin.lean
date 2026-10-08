import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [NeZero n]
  {f : Fin m → Fin n → ℝ} :
-- imply
  (fun i => ArgMin Set.univ fun j => f i j) = fun i => ArgMin Set.univ (f i) :=
-- proof
  rfl


-- created on 2026-10-08
