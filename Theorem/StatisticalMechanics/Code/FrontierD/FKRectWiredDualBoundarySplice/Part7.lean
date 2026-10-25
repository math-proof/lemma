/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectWiredDualRightBoundaryAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    e ∈ fkRectWiredDualRightBoundaryAddedEdgeList R omega ↔
      e ∈ fkRectDualRightBoundaryEdgeList R ∧
        e ∈ fkRectWiredDualAddedEdges R omega := by
  classical
  simp [fkRectWiredDualRightBoundaryAddedEdgeList]


end
end StatMech.FrontierD
