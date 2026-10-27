import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Majority
open Finset BigOperators Real Filter


namespace BooleanFourier

/--
[noiseSensitivity_majority_limit_lt_half](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary43Majority.lean)
-/
@[path]
lemma noiseSensitivity_majority_limit_lt_half
  {δ : ℝ}
-- given
  (hδ_pos : 0 < δ)
  (hδ_lt : δ < 1 / 2) :
-- imply
  (1 / Real.pi) * Real.arccos (1 - 2 * δ) < 1 / 2 := by
-- proof
  have h1 : (0 : ℝ) < 1 - 2 * δ := by linarith
  have h3 : Real.arccos (1 - 2 * δ) < Real.pi / 2 := by
    rw [show Real.pi / 2 = Real.arccos 0 from (Real.arccos_zero).symm]
    exact Real.arccos_lt_arccos (by linarith : (-1 : ℝ) ≤ 0) h1
      (by linarith : (1 : ℝ) - 2 * δ ≤ 1)
  calc (1 / Real.pi) * Real.arccos (1 - 2 * δ)
    < (1 / Real.pi) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_left h3 (div_pos one_pos Real.pi_pos)
    _ = 1 / 2 := by field_simp

end BooleanFourier

namespace BooleanFourier

/--
[majority_not_maximally_noiseSensitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary43Majority.lean)
-/
@[path]
lemma majority_not_maximally_noiseSensitive
  {δ : ℝ}
-- given
  (hδ_pos : 0 < δ)
  (hδ_lt : δ < 1 / 2) :
-- imply
  Filter.Tendsto (fun k => noiseSensitivityReal δ (majorityFn (2 * k + 1))) Filter.atTop (nhds ((1 / Real.pi) * Real.arccos (1 - 2 * δ))) ∧ (1 / Real.pi) * Real.arccos (1 - 2 * δ) < 1 / 2 := by
-- proof
  exact ⟨noiseSensitivity_majority_tendsto hδ_pos (le_of_lt hδ_lt),
    noiseSensitivity_majority_limit_lt_half hδ_pos hδ_lt⟩

end BooleanFourier


-- created on 2026-10-23
-- updated on 2026-10-27
