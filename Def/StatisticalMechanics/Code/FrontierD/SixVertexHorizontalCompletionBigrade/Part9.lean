/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalCompletionBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalCompletionBigrade.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalAdmissibleSeamRowEquivPowerset
    {T : EvenTorus} {horizontal : SixVertexHorizontalField T}
    (completion : SixVertexVerticalCompletion T horizontal)
    (sector : Fin (T.width + 1)) :
    SixVertexHorizontalAdmissibleSeamRow T sector horizontal ≃
      {row : Finset (Fin T.width) //
        row ∈ ((sixVertexHorizontalTrueAllowedColumns horizontal).powersetCard
            sector.val).filter
          (sixVertexHorizontalForcedTrueColumns horizontal ⊆ ·)} where
  toFun row := ⟨row.1.1, by
    have hsub :=
      (sixVertexHorizontalAdmissibleSeamRow_iff_subset
        completion sector row.1).mp row.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hsub.2, row.1.2⟩, hsub.1⟩⟩
  invFun row :=
    let sectorRow : SixVertexSector T.width sector.val :=
      ⟨row.1, (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp row.2).1).2⟩
    ⟨sectorRow,
      (sixVertexHorizontalAdmissibleSeamRow_iff_subset
        completion sector sectorRow).mpr
          ⟨(Finset.mem_filter.mp row.2).2,
            (Finset.mem_powersetCard.mp
              (Finset.mem_filter.mp row.2).1).1⟩⟩
  left_inv row := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv row := by
    apply Subtype.ext
    rfl


end
end StatMech.FrontierD
