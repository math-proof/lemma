import Mathlib
import sympy.Basic
import Theorem.Analysis.Complex.Wiman.Filevych
open Filter MeasureTheory Set
open Complex


namespace Complex

/--
[tendsto_wimanMaximumTerm_exp_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/Filevych.lean)
-/
@[path]
lemma tendsto_wimanMaximumTerm_exp_atTop
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  Tendsto (fun x : ℝ => wimanMaximumTerm f (Real.exp x)) atTop atTop :=
-- proof
  (tendsto_wimanMaximumTerm_atTop f hf htrans).comp Real.tendsto_exp_atTop

end Complex

namespace Complex

/--
[exists_wiman_radius_two_thirds](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/Filevych.lean)
-/
@[path]
lemma exists_wiman_radius_two_thirds
  {f : ℂ → ℂ}
  {R : ℝ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∃ r : ℝ, R < r ∧ wimanMaximumModulus f r ≤
    wimanMaximumTerm f r *
    Real.log (wimanMaximumTerm f r) ^ (2 / 3 : ℝ) := by
-- proof
  obtain ⟨C, x₀, hC, hfinite, hmajorant⟩ :=
    wimanMajorant_bound_off_exceptionalSet f hf htrans
  obtain ⟨U, _hU, habsorb⟩ :=
    eventually_absorb_corrected_wiman_exponent C hC
  have hrequirements :
    ∀ᶠ x : ℝ in atTop,
      x₀ ≤ x ∧ R < Real.exp x ∧
        U ≤ wimanMaximumTerm f (Real.exp x) := by
    filter_upwards [eventually_ge_atTop x₀,
      Real.tendsto_exp_atTop.eventually (eventually_gt_atTop R),
      (tendsto_wimanMaximumTerm_exp_atTop f hf htrans).eventually
        (eventually_ge_atTop U)] with x hx₀ hR hU
    exact ⟨hx₀, hR, hU⟩
  obtain ⟨X, hX⟩ := eventually_atTop.1 hrequirements
  obtain ⟨x, hXx, hxgood⟩ :=
    MeasureTheory.exists_gt_not_mem_of_volume_lt_top
      (wimanExceptionalSet f x₀) hfinite X
  obtain ⟨hx₀, hR, hU⟩ := hX x hXx.le
  let r : ℝ := Real.exp x
  have hr : 0 < r := by
    simpa only [r] using Real.exp_pos x
  have hUterm : U ≤ wimanMaximumTerm f r := by
    simpa only [r] using hU
  have htermModulus :
    wimanMaximumTerm f r ≤ wimanMaximumModulus f r :=
    wimanMaximumTerm_le_wimanMaximumModulus f hf hr
  have hmodulusMajorant :
    wimanMaximumModulus f r ≤ wimanMajorant f r :=
    wimanMaximumModulus_le_wimanMajorant f hf hr.le
  have htermMajorant :
    wimanMaximumTerm f r ≤ wimanMajorant f r :=
    htermModulus.trans hmodulusMajorant
  have hcorrected :
    wimanMajorant f r ≤
      C * wimanMaximumTerm f r *
        (1 + Real.log (wimanMajorant f r) ^ (81 / 128 : ℝ)) := by
    simpa only [r, wimanGrowth] using hmajorant x hx₀ hxgood
  have habsorbed :
    wimanMajorant f r ≤
      wimanMaximumTerm f r *
        Real.log (wimanMaximumTerm f r) ^ (2 / 3 : ℝ) :=
    habsorb (wimanMaximumTerm f r) (wimanMajorant f r)
      hUterm htermMajorant hcorrected
  exact ⟨r, by simpa only [r] using hR, hmodulusMajorant.trans habsorbed⟩
end



-- created on 2026-10-20
-- updated on 2026-10-23
