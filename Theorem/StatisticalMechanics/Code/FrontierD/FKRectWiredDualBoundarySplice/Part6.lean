/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectDualRightBoundaryEdgeList
    (R : FKRectTorus) (e : R.EdgeIndex) :
    e ∈ fkRectDualRightBoundaryEdgeList R ↔
      ∃ y : Fin R.height, fkRectDualRightBoundaryEdge R y = e := by
  simp [fkRectDualRightBoundaryEdgeList]

theorem fkRectDualRightBoundaryEdgeList_subset_dualCutEdges
    (R : FKRectTorus) {e : R.EdgeIndex}
    (he : e ∈ fkRectDualRightBoundaryEdgeList R) :
    e ∈ fkRectDualCutEdges R := by
  obtain ⟨y, rfl⟩ := (mem_fkRectDualRightBoundaryEdgeList R e).1 he
  exact fkRectDualRightBoundaryEdge_mem_dualCutEdges R y


end
end StatMech.FrontierD
