import sympy.series.limits
import sympy.Basic


/--
py `Real.LimMul.eq.MulLimS.of.Ne_0.EqLim.EqLim`
(ℝ-valued form; py uses extended reals with \(g\)'s limit nonzero).
-/
@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ y z : ℝ}
-- given
  (hf : lim [x → x₀] f x = y)
  (hg : lim [x → x₀] g x = z)
  (_ : z ≠ 0) :
-- imply
  lim [x → x₀] (f x * g x) = (lim [x → x₀] f x) * (lim [x → x₀] g x) := by
-- proof
  rw [hf.limUnder_eq, hg.limUnder_eq]
  apply hf.mul hg


-- created on 2021-08-14
