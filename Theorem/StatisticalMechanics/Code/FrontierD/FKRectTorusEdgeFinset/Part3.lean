/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectFinsetClusterCount_empty (R : FKRectTorus) :
    fkRectFinsetClusterCount R ∅ = Fintype.card R.Vertex := by
  unfold fkRectFinsetClusterCount fkRectNumClusters
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R ∅)
  have hG : G = (⊥ : SimpleGraph R.Vertex) :=
    fkRectOpenGraph_configurationOfEdges_empty R
  calc
    Fintype.card G.ConnectedComponent =
        Fintype.card (⊥ : SimpleGraph R.Vertex).ConnectedComponent := by
      exact Fintype.card_congr
        (Equiv.cast (congrArg
          (fun H : SimpleGraph R.Vertex => H.ConnectedComponent) hG))
    _ = Fintype.card R.Vertex := by
      simpa only [Nat.card_eq_fintype_card] using
        (card_components_bot (V := R.Vertex))

end
end StatMech.FrontierD
