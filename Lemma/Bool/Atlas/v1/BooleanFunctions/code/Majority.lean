import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Claim21Lec10
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Claim21Lec10
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.DisagreementStability
import sympy.atlas.v1.Atlas.BooleanFunctions.code.DisagreementStability
open Finset BigOperators Real Filter


namespace BooleanFourier

/--
[noiseSensitivity_majority_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Majority.lean)
-/
@[path]
lemma noiseSensitivity_majority_tendsto
  {δ : ℝ}
-- given
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1 / 2) :
-- imply
  Filter.Tendsto (fun k => noiseSensitivityReal δ (majorityFn (2 * k + 1))) Filter.atTop (nhds ((1 / Real.pi) * Real.arccos (1 - 2 * δ))) := by
-- proof
  have hρ_gt : -1 < 1 - 2 * δ := by linarith
  have hρ_lt : 1 - 2 * δ < 1 := by linarith
  have hstab := noiseStability_majority_tendsto (1 - 2 * δ) hρ_gt hρ_lt
  have hcont : Filter.Tendsto
    (fun k => (1 - noiseStability (1 - 2 * δ) (majorityFn (2 * k + 1))) / 2)
    Filter.atTop
    (nhds ((1 - 2 / Real.pi * Real.arcsin (1 - 2 * δ)) / 2)) :=
    (Filter.Tendsto.const_sub 1 hstab).div_const 2
  have hfun_eq : (fun k => noiseSensitivityReal δ (majorityFn (2 * k + 1))) =
    (fun k => (1 - noiseStability (1 - 2 * δ) (majorityFn (2 * k + 1))) / 2) := by
    funext k
    exact noiseSensitivityReal_eq δ (majorityFn (2 * k + 1))
  rw [hfun_eq]
  suffices heq : (1 - 2 / Real.pi * Real.arcsin (1 - 2 * δ)) / 2 =
    (1 / Real.pi) * Real.arccos (1 - 2 * δ) by
    rwa [← heq]
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

end BooleanFourier


-- created on 2026-10-23
