import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [NeZero m]
  {f g : ℝ → Fin m → ℝ}
  {x a b : ℝ} :
-- imply
  ArgMax Set.univ (if a > b then f x else g x) = if a > b then ArgMax Set.univ (f x) else ArgMax Set.univ (g x) := by
-- proof
  split_ifs <;> rfl


-- created on 2021-12-17
