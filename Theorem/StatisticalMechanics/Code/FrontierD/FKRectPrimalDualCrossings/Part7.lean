/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectPrimalDualCrossingRepresentativeSourceIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    (fkRectPrimalDualCrossingRepresentativeSourceIndices R eta).card =
      fkRectPrimalDualHorizontalCrossingClusterCount R eta := by
  classical
  unfold fkRectPrimalDualCrossingRepresentativeSourceIndices
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_sum]
    rfl
  · exact fkRectPrimalDualCrossingRepresentativeSourceIndex_injective R eta

theorem fkRectPrimalDualCrossingRepresentativeSourceIndices_subset_sources
    (R : FKRectTorus) (eta : R.Configuration) :
    ∀ i ∈ fkRectPrimalDualCrossingRepresentativeSourceIndices R eta,
      FKRectPrimalDualCrossingSource R eta i := by
  classical
  intro i hi
  unfold fkRectPrimalDualCrossingRepresentativeSourceIndices at hi
  rw [Finset.mem_image] at hi
  rcases hi with ⟨C, hCuniv, rfl⟩
  rcases C with C | C
  · simpa [FKRectPrimalDualCrossingSource,
      fkRectPrimalDualCrossingRepresentativeSourceIndex] using
      (fkRectRawHorizontalCrossingRepresentative_source R
        (fkRectForceCutClosed R eta) C)
  · simpa [FKRectPrimalDualCrossingSource,
      fkRectPrimalDualCrossingRepresentativeSourceIndex] using
      (fkRectRawHorizontalCrossingRepresentative_source R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R eta)) C)

theorem fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawPrimalDualHorizontalCrossingClusterCount R eta ≤
      2 * R.height := by
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount
  have hp := fkRectRawHorizontalCrossingClusterCount_le_height R eta
  have hd := fkRectRawHorizontalCrossingClusterCount_le_height R
    (fkRectDualConfigurationEquiv R eta)
  omega

theorem fkRectPrimalDualHorizontalCrossingClusterCount_le_two_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectPrimalDualHorizontalCrossingClusterCount R eta <=
      2 * R.height :=
  fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height R _

end
end StatMech.FrontierD
