import Initialize.Tactic.Attr.Basic
import Macro.Order.ExprWithLimits


@[path]
private lemma main
  [NeZero n]
  {f : Fin m → Fin n → ℝ} :
-- imply
  (fun i => ArgMin Set.univ fun j => f i j) = fun i => ArgMin Set.univ (f i) :=
-- proof
  rfl


-- created on 2021-12-17
