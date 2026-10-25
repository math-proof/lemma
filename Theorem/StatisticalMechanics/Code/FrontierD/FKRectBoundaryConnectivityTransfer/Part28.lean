/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part30
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundarySeamGraph_eq_edgeRun
    {W : Nat} (hW : 0 < W) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) :
    fkRectBoundarySeamGraph hW state eta =
      finiteBoundaryEdgeRun id state
        (fkRectBoundaryOpenSeamEdges hW eta) := by
  classical
  ext u v
  rw [finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundarySeamGraph fkRectBoundaryOpenSeamEdges
    fkRectBoundaryOpenLayerIndices
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and, SimpleGraph.edge_adj, id_eq]
  constructor
  · rintro (hstate | ⟨a, ha, huv⟩)
    · exact Or.inl hstate
    · have hne : u ≠ v := by
        intro huvEq
        apply fkRectBoundarySeamEdgeEndpoints_ne hW a
        rcases huv with huv | huv
        · exact huv.1.trans (huvEq.trans huv.2.symm)
        · exact (huv.2.trans (huvEq.trans huv.1.symm)).symm
      refine Or.inr ⟨fkRectBoundarySeamEdgeEndpoints hW a,
        ⟨a, ha, rfl⟩, ⟨?_, hne⟩⟩
      rcases huv with huv | huv
      · exact Or.inl ⟨huv.1.symm, huv.2.symm⟩
      · exact Or.inr ⟨huv.2.symm, huv.1.symm⟩
  · rintro (hstate | ⟨e, ⟨a, ha, rfl⟩, hedge⟩)
    · exact Or.inl hstate
    · refine Or.inr ⟨a, ha, ?_⟩
      rcases hedge.1 with hedge | hedge
      · exact Or.inl ⟨hedge.1.symm, hedge.2.symm⟩
      · exact Or.inr ⟨hedge.2.symm, hedge.1.symm⟩


end
end StatMech.FrontierD
