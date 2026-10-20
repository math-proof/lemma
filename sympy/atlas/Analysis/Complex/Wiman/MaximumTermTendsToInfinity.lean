/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean -/

import sympy.atlas.Analysis.Complex.Wiman.InfiniteTaylorSupport
import sympy.atlas.Analysis.Complex.Wiman.MaximumTermAttained
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Finset.Basic

namespace Complex

open Filter

/-- The maximum Taylor term of a transcendental entire function tends to infinity. -/
theorem tendsto_wimanMaximumTerm_atTop
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    Tendsto (wimanMaximumTerm f) atTop atTop := by
  obtain ⟨n, hnmem, hnpos⟩ :=
    (infinite_support_wimanTaylorCoefficient f hf htrans).exists_gt 0
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hcoeff : wimanTaylorCoefficient f n ≠ 0 := by
    simpa only [Function.mem_support] using hnmem
  have hcoeffnorm : 0 < ‖wimanTaylorCoefficient f n‖ := norm_pos_iff.mpr hcoeff
  have hterm : Tendsto (fun r : ℝ ↦ wimanTerm f r n) atTop atTop := by
    have hraw :
        Tendsto (fun r : ℝ ↦ ‖wimanTaylorCoefficient f n‖ * r ^ n) atTop atTop :=
      tendsto_const_mul_pow_atTop hn hcoeffnorm
    refine hraw.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp only [wimanTerm, abs_of_nonneg hr]
  refine tendsto_atTop_mono' atTop ?_ hterm
  filter_upwards with r
  exact wimanTerm_le_wimanMaximumTerm f hf r n

/-- Eventually the maximum Taylor term is greater than one. -/
theorem eventually_one_lt_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∀ᶠ r : ℝ in atTop, 1 < wimanMaximumTerm f r :=
  (tendsto_wimanMaximumTerm_atTop f hf htrans).eventually (eventually_gt_atTop 1)

/-- Eventually the logarithm of the maximum Taylor term is positive. -/
theorem eventually_pos_log_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∀ᶠ r : ℝ in atTop, 0 < Real.log (wimanMaximumTerm f r) := by
  filter_upwards [eventually_one_lt_wimanMaximumTerm f hf htrans] with r hr
  exact Real.log_pos hr

end Complex
