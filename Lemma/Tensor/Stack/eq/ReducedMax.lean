import sympy.Basic
import Macro.Order.ExprWithLimits


@[path]
private lemma main
  [SupSet β]
  {a : ι → κ → β} :
-- imply
  (fun i => Maxima Set.univ (a i)) = fun i => Maxima Set.univ fun j => a i j :=
-- proof
  rfl


-- created on 2019-10-20
