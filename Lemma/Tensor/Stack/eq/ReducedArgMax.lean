import Initialize.Tactic.Attr.Basic
import Macro.Order.ExprWithLimits


@[path]
private lemma main
  [NeZero n]
  {x : Fin m → Fin n → ℝ} :
-- imply
  (fun i => ArgMax Set.univ (x i)) = fun i => ArgMax Set.univ fun j => x i j :=
-- proof
  rfl


-- created on 2021-12-20
