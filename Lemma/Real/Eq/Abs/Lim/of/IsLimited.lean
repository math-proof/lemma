import Lemma.Real.Eq.Lim.Abs.of.IsNegative
import Lemma.Real.Eq.Lim.Abs.of.IsPositive
import Lemma.Real.Eq_0.Lim.Abs.of.Eq_0
import sympy.series.limits
open Real


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x₀ y : ℝ}
-- given
  (h : lim [x → x₀] g x = y) :
-- imply
  lim [x → x₀] |g x| = |y| := by
-- proof
  exact h.abs


-- created on 2026-10-07
