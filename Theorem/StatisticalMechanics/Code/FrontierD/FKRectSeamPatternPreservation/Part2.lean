/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamPatternPreservation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Def.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualPullbackUnitGap_eq_verticalSeam (R : FKRectTorus) :
    fkRectDualEdgeToEdge R (fkRectUnitLeftBarrierGap R) =
      fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R) := by
  rfl

theorem fkRectEdgeToDualEdge_unitVerticalSeam (R : FKRectTorus) :
    fkRectEdgeToDualEdge R
        (fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R)) =
      fkRectUnitLeftBarrierGap R := by
  rfl


theorem fkRectForceDualPullbackUnitPattern_verticalSeam_open
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega
        (fkRectVerticalSeamEdgeAt R (fkRectUnitGapColumn R)) = true := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges,
    fkRectForceIndexedPattern_of_mem]
  · unfold fkRectDualPullbackConfiguration
    rw [fkRectEdgeToDualEdge_unitVerticalSeam]
    simp [fkRectAllButOneOpenConfiguration]
  · simp [mem_fkRectHorizontalCutEdges_iff, fkRectVerticalSeamEdgeAt,
      fkRectRowZeroVertex]


theorem fkRectForceDualPullbackUnitPattern_attachment_eq
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega
        (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) =
      omega (fkRectRowZeroAttachmentEdgeAt R (fkRectUnitGapColumn R)) := by
  rw [fkRectDualPullbackIndexSet_horizontalCutEdges,
    fkRectForceIndexedPattern_of_not_mem]
  simp [mem_fkRectHorizontalCutEdges_iff,
    fkRectRowZeroAttachmentEdgeAt, fkRectRowOneVertex]


theorem fkRectForceDualPullbackUnitPattern_verticalWinding_of_chain
    (R : FKRectTorus) (omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R 1 1 (R.height - 1) ×
      FKRectRightStripBandVertex R 1 1 (R.height - 1)))
    (hpair :
      (fkRectRightBandRowOne R 1 (fkRectUnitGapColumn R) (by rfl),
        fkRectRightBandLastRow R 1 (fkRectUnitGapColumn R) (by rfl)) ∈ t)
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R 1 1 (R.height - 1) -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R 1 1 (R.height - 1)) t)
    (hattach :
      omega (fkRectRowZeroAttachmentEdgeAt R
        (fkRectUnitGapColumn R)) = true) :
    fkRectForceIndexedPattern R
        (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R))
        (fkRectDualPullbackConfiguration R
          (fkRectAllButOneOpenConfiguration R
            (fkRectUnitLeftBarrierGap R))) omega ∈
      fkRectVerticalWindingEvent R := by
  let eta := fkRectDualPullbackConfiguration R
    (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))
  let forced := fkRectForceIndexedPattern R
    (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega
  apply fkRectVerticalWindingEvent_of_rightBand_chain R 1
    (fkRectUnitGapColumn R) (by rfl) forced t hpair
  · exact fkRectForceDualPullbackSeam_preserves_rightBand_chain
      R 1 1 (R.height - 1) (by rfl) eta omega t hchain
  · exact fkRectForceDualPullbackUnitPattern_verticalSeam_open R omega
  · dsimp [forced, eta]
    rw [fkRectForceDualPullbackUnitPattern_attachment_eq]
    exact hattach

end
end StatMech.FrontierD
