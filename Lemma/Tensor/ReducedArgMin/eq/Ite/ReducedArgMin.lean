import Initialize.Tactic.Attr.Basic
import Syntax.Order.ExprWithLimits


@[path]
private lemma main
  [NeZero m]
  {f g : ℝ → Fin m → ℝ}
  {x a b : ℝ} :
-- imply
  min⁻¹ Set.univ (if a > b then f x else g x) = if a > b then min⁻¹ Set.univ (f x) else min⁻¹ Set.univ (g x) := by
-- proof
  split_ifs <;> rfl


-- created on 2021-12-17
