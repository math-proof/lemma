import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  sInf (f '' S) ≤ Minima S f := by
-- proof
  exact le_of_eq rfl


-- created on 2019-01-03
