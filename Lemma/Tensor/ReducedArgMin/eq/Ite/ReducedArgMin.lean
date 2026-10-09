import sympy.Basic
import sympy.concrete.expr_with_limits


@[path]
private lemma main
  [NeZero m]
  {f g : ℝ → Fin m → ℝ}
  {x a b : ℝ} :
-- imply
  ArgMin Set.univ (if a > b then f x else g x) = if a > b then ArgMin Set.univ (f x) else ArgMin Set.univ (g x) := by
-- proof
  split_ifs <;> rfl


-- created on 2026-10-08
