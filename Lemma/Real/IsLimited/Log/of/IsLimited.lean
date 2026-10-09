import Lemma.Real.EqLog.of.IsLimited
import sympy.series.limits
open Real Set


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x₀ y : ℝ}
-- given
  (h : lim [x → x₀] g x = y)
  (hy : y ∈ Ioi 0) :
-- imply
  ∃ z : ℝ, lim [x → x₀] log (g x) = z := by
-- proof
  apply Exists.intro (log y)
  apply EqLog.of.IsLimited h hy


-- created on 2026-10-07
