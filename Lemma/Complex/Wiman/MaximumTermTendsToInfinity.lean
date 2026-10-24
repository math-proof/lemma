import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.InfiniteTaylorSupport
import Lemma.Complex.Wiman.InfiniteTaylorSupport
import Lemma.Complex.Wiman.MaximumTermAttained
import sympy.atlas.Analysis.Complex.Wiman.MaximumTermAttained
open Filter


namespace Complex

/--
[tendsto_wimanMaximumTerm_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean)
-/
@[path]
lemma tendsto_wimanMaximumTerm_atTop
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  Tendsto (wimanMaximumTerm f) atTop atTop := by
-- proof
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

end Complex

namespace Complex

/--
[eventually_one_lt_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean)
-/
@[path]
lemma eventually_one_lt_wimanMaximumTerm
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∀ᶠ r : ℝ in atTop, 1 < wimanMaximumTerm f r :=
-- proof
  (tendsto_wimanMaximumTerm_atTop f hf htrans).eventually (eventually_gt_atTop 1)

end Complex

namespace Complex

/--
[eventually_pos_log_wimanMaximumTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/MaximumTermTendsToInfinity.lean)
-/
@[path]
lemma eventually_pos_log_wimanMaximumTerm
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∀ᶠ r : ℝ in atTop, 0 < Real.log (wimanMaximumTerm f r) := by
-- proof
  filter_upwards [eventually_one_lt_wimanMaximumTerm f hf htrans] with r hr
  exact Real.log_pos hr

end Complex


-- created on 2026-10-20
-- updated on 2026-10-23
