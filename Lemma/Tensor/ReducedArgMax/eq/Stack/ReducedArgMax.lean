import Initialize.Tactic.Attr.Basic
import Syntax.Order.ExprWithLimits


@[path]
private lemma main
  [NeZero n]
  {f : Fin m → Fin n → ℝ} :
-- imply
  (fun i => «max⁻¹» Set.univ fun j => f i j) = fun i => «max⁻¹» Set.univ (f i) :=
-- proof
  rfl


-- created on 2021-12-17
-- updated on 2026-11-13
