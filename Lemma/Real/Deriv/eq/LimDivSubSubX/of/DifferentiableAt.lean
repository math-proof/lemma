import Mathlib.Analysis.Calculus.Deriv.Slope
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : DifferentiableAt ℝ f x₀) :
-- imply
  deriv f x₀ = lim [x → x₀] ((f x - f x₀) / (x - x₀)) := by
-- proof
  have hslope := h.hasDerivAt.tendsto_slope
  have hfun : (fun x => (f x - f x₀) / (x - x₀)) = slope f x₀ := by
    ext x
    simp [slope, div_eq_inv_mul]
  rw [hfun, hslope.limUnder_eq, h.hasDerivAt.deriv]


-- created on 2020-04-06
