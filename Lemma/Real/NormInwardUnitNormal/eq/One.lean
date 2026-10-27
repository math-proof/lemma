import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Reflection.InnerProductWalls
import Lemma.Finset.Inner.ne.Zero.of.Nonempty.All_Ne_0
open Set HyperplaneArrangement
open scoped InnerProductSpace


namespace HyperplaneArrangement

/--
[norm_inwardUnitNormal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/InnerProductWalls.lean)
-/
@[path]
private lemma norm_inwardUnitNormal
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {arr : HyperplaneArrangement E}
  {C : arr.Chamber}
  {η : AffineHyperplane E}
  [Decidable (ChamberInPositiveHalfSpace C η)] :
-- imply
  ‖inwardUnitNormal C η‖ = 1 := by
-- proof
  unfold inwardUnitNormal
  split
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr η.normal_ne_zero
  · rw [norm_smul, norm_inv, norm_norm, norm_neg, inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr η.normal_ne_zero

end HyperplaneArrangement

namespace HyperplaneArrangement

end HyperplaneArrangement


-- created on 2026-10-23
-- updated on 2026-10-26
