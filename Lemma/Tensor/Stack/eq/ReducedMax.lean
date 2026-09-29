import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [SupSet β]
  {a : ι → κ → β} :
-- imply
  (fun i => Maxima Set.univ (a i)) = fun i => Maxima Set.univ fun j => a i j :=
-- proof
  rfl


-- created on 2026-09-27
