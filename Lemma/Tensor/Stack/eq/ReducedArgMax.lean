import Initialize.Tactic.Attr.Basic
import Syntax.Order.ExprWithLimits


@[path]
private lemma main
  [NeZero n]
  {x : Fin m → Fin n → ℝ} :
-- imply
  (fun i => «max⁻¹» Set.univ (x i)) = fun i => «max⁻¹» Set.univ fun j => x i j :=
-- proof
  rfl


-- created on 2021-12-20
-- updated on 2026-11-13
