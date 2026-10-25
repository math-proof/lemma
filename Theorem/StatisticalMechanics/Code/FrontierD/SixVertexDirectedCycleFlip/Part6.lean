/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusFlip_upCount
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    (sixVertexUpCount
        (svTorusVerticalRows T (sixVertexTorusFlip mask omega)
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) +
        sixVertexTorusFlipSeamDelta mask omega := by
  let targetRow := svTorusVerticalRows T (sixVertexTorusFlip mask omega)
    (svFinLast T.height_pos)
  let sourceRow := svTorusVerticalRows T omega (svFinLast T.height_pos)
  have htarget : (∑ i, ((targetRow i).toNat : Int)) =
      (sixVertexUpCount targetRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount targetRow
  have hsource : (∑ i, ((sourceRow i).toNat : Int)) =
      (sixVertexUpCount sourceRow : Int) := by
    exact_mod_cast sum_bool_toNat_eq_sixVertexUpCount sourceRow
  change (sixVertexUpCount targetRow : Int) =
    (sixVertexUpCount sourceRow : Int) +
      ∑ i, (((targetRow i).toNat : Int) - ((sourceRow i).toNat : Int))
  rw [Finset.sum_sub_distrib, htarget, hsource]
  ring


theorem sixVertexTorusFlipSeamDelta_after_flip
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    sixVertexTorusFlipSeamDelta mask (sixVertexTorusFlip mask omega) =
      -sixVertexTorusFlipSeamDelta mask omega := by
  unfold sixVertexTorusFlipSeamDelta
  simp only [sixVertexTorusFlip_self]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro column _
  ring


theorem sixVertexTorusFlipSeamDelta_maskXor
    {T : EvenTorus} (first second omega : SixVertexArrows T) :
    sixVertexTorusFlipSeamDelta
        (sixVertexTorusMaskXor first second) omega =
      sixVertexTorusFlipSeamDelta first omega +
        sixVertexTorusFlipSeamDelta second
          (sixVertexTorusFlip first omega) := by
  unfold sixVertexTorusFlipSeamDelta
  rw [sixVertexTorusFlip_maskXor_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro column _
  ring

end
end StatMech.FrontierD
