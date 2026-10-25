/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexHorizontalSectorCompletion_eq_choose
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (sector : Fin (T.width + 1)) :
    Fintype.card
        (SixVertexHorizontalSectorCompletion T sector horizontal) =
      if (sixVertexHorizontalForcedTrueColumns horizontal).card <= sector.val
      then Nat.choose
        ((sixVertexHorizontalTrueAllowedColumns horizontal).card -
          (sixVertexHorizontalForcedTrueColumns horizontal).card)
        (sector.val -
          (sixVertexHorizontalForcedTrueColumns horizontal).card)
      else 0 := by
  rw [Fintype.card_congr
      (sixVertexHorizontalSectorCompletionEquivAdmissibleSeamRow
        T sector horizontal),
    Fintype.card_congr
      (sixVertexHorizontalAdmissibleSeamRowEquivPowerset
        completion sector),
    Fintype.card_coe]
  split_ifs with hforced
  · exact Finset.card_filter_powersetCard_subset
      (sixVertexHorizontalForcedTrueColumns horizontal)
      (sixVertexHorizontalTrueAllowedColumns horizontal)
      sector.val
      (sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal)
      hforced
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro row hrow
    have hsubset := (Finset.mem_filter.mp hrow).2
    have hcard := Finset.card_le_card hsubset
    have hrowCard := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hrow).1).2
    omega


end
end StatMech.FrontierD
