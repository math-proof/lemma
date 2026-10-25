/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectWiredDualAddedEdgeList_toFinset
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkRectWiredDualAddedEdgeList R omega).toFinset =
      fkRectWiredDualAddedEdges R omega := by
  classical
  simp [fkRectWiredDualAddedEdgeList]

theorem fkRectInsert_wiredDualAddedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectInsertEdgeList R
        (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega))
        (fkRectWiredDualAddedEdgeList R omega) =
      fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪
        fkRectWiredDualAddedEdges R omega := by
  rw [fkRectInsertEdgeList_eq_union_toFinset,
    fkRectWiredDualAddedEdgeList_toFinset]


theorem fkRectDual_forceCutClosed_eq_configurationOfInsertedEdgeList
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) =
      fkRectConfigurationOfEdges R
        (fkRectInsertEdgeList R
          (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega))
          (fkRectWiredDualAddedEdgeList R omega)) := by
  rw [fkRectInsert_wiredDualAddedEdgeList]
  exact fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges R omega


end
end StatMech.FrontierD
