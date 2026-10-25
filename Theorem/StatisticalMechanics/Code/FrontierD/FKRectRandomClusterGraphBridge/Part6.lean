/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectGraphOpenGraph_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectGraphOpenGraph R (fkRectConfigurationGraphEquiv R omega) =
      fkRectOpenGraph R omega := by
  ext x y
  constructor
  · rintro ⟨e, he, hxy⟩
    let a := (fkRectEdgeGraphEquiv R).symm e
    refine ⟨a, ?_, ?_⟩
    · exact he
    · rw [fkRectEdgeGraphEquiv_symm_indexedEdge]
      exact hxy
  · rintro ⟨a, ha, hxy⟩
    refine ⟨fkRectEdgeGraphEquiv R a, ?_, ?_⟩
    · exact fkRectConfigurationGraphEquiv_apply_edge R omega a |>.trans ha
    · simpa using hxy


theorem fkRectGraph_clusterCount_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (fkRectGraphOpenGraph R
          (fkRectConfigurationGraphEquiv R omega)).ConnectedComponent =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  rw [fkRectGraphOpenGraph_configurationGraphEquiv]
  simp only [← Nat.card_eq_fintype_card]


end
end StatMech.FrontierD
