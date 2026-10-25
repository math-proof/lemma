/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVerticalSeamEdgeAt_indexedEdge
    (R : FKRectTorus) (x : Fin R.width) :
    fkRectTorusIndexedEdge R (fkRectVerticalSeamEdgeAt R x) =
      s(fkRectRowZeroVertex R x, fkRectLastRowVertex R x) := by
  simp [fkRectVerticalSeamEdgeAt, fkRectRowZeroVertex,
    fkRectLastRowVertex, fkRectTorusIndexedEdge, svCyclicPred_zero]

theorem fkRectRowZeroAttachmentEdgeAt_indexedEdge
    (R : FKRectTorus) (x : Fin R.width) :
    fkRectTorusIndexedEdge R (fkRectRowZeroAttachmentEdgeAt R x) =
      s(fkRectRowOneVertex R x, fkRectRowZeroVertex R x) := by
  unfold fkRectRowZeroAttachmentEdgeAt fkRectRowOneVertex
  simp only [fkRectTorusIndexedEdge, if_true]
  rw [show SixVertexArrows.cyclicPred R.height_pos
      (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height) =
        (⟨0, R.height_pos⟩ : Fin R.height) by
    apply Fin.ext
    rw [fkRectCyclicPred_val]
    simp]
  rfl

theorem fkRectVerticalSeamEdgeAt_crosses
    (R : FKRectTorus) (x : Fin R.width) :
    fkRectCrossesVerticalSeam R
      (fkRectTorusIndexedEdge R (fkRectVerticalSeamEdgeAt R x)) := by
  apply fkRectHorizontalCutEdge_crossesVerticalSeam
  simp [mem_fkRectHorizontalCutEdges_iff, fkRectVerticalSeamEdgeAt,
    fkRectRowZeroVertex]

theorem fkRectRowZeroAttachmentEdgeAt_not_crosses
    (R : FKRectTorus) (x : Fin R.width) :
    ¬ fkRectCrossesVerticalSeam R
      (fkRectTorusIndexedEdge R
        (fkRectRowZeroAttachmentEdgeAt R x)) := by
  rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge,
    fkRectCrossesVerticalSeam_mk]
  change ¬ ((1 = 0 ∧ 0 + 1 = R.height) ∨
    (0 = 0 ∧ 1 + 1 = R.height))
  have hheight := R.height_gt_two
  omega


end
end StatMech.FrontierD
