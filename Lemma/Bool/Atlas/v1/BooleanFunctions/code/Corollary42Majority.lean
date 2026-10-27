import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Majority
open Finset BigOperators Real Filter


namespace BooleanFourier

/--
[noiseSensitivity_majority_limit_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary42Majority.lean)
-/
@[path]
lemma noiseSensitivity_majority_limit_pos
  {δ : ℝ}
-- given
  (hδ_pos : 0 < δ) :
-- imply
  0 < (1 / Real.pi) * Real.arccos (1 - 2 * δ) := by
-- proof
  apply mul_pos
  · exact div_pos one_pos Real.pi_pos
  · rw [Real.arccos_pos]
    linarith

end BooleanFourier

namespace BooleanFourier

/--
[majority_noiseSensitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary42Majority.lean)
-/
@[path]
lemma majority_noiseSensitive
  {δ : ℝ}
-- given
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1 / 2) :
-- imply
  Filter.Tendsto (fun k => noiseSensitivityReal δ (majorityFn (2 * k + 1))) Filter.atTop (nhds ((1 / Real.pi) * Real.arccos (1 - 2 * δ))) ∧ 0 < (1 / Real.pi) * Real.arccos (1 - 2 * δ) :=
-- proof
  ⟨noiseSensitivity_majority_tendsto hδ_pos hδ_le,
    noiseSensitivity_majority_limit_pos hδ_pos⟩

end BooleanFourier

namespace BooleanFourier

/--
[majority_noiseSensitivity_eventually_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Corollary42Majority.lean)
-/
@[path]
lemma majority_noiseSensitivity_eventually_pos
  {δ : ℝ}
-- given
  (hδ_pos : 0 < δ)
  (hδ_le : δ ≤ 1 / 2) :
-- imply
  ∀ᶠ k in Filter.atTop, 0 < noiseSensitivityReal δ (majorityFn (2 * k + 1)) := by
-- proof
  have hlim := noiseSensitivity_majority_tendsto hδ_pos hδ_le
  have hpos := noiseSensitivity_majority_limit_pos hδ_pos
  exact hlim.eventually (eventually_gt_nhds hpos)

end BooleanFourier


-- created on 2026-10-23
-- updated on 2026-10-27
