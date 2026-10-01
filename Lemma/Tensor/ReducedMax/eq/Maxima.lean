import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ} :
-- imply
  sSup (f '' S) = Maxima S f := by
-- proof
  rfl


-- created on 2018-12-31
