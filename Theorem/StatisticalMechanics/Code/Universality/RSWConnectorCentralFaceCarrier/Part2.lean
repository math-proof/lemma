/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorFourTraceFaceCutGraph_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) :
    (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧
        sharedPrimalEdge f g ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  rw [rlc_connectorFourTraceFaceCutGraph, whb_faceRegion_adj]
  constructor
  · rintro ⟨hfg, hwall⟩
    refine ⟨hfg, ?_⟩
    have hlat : sharedPrimalEdge f g ∈ (hypercubicLattice 2).edgeSet := by
      obtain ⟨u, v, huv, huvAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
      rw [huv, SimpleGraph.mem_edgeSet]
      exact huvAdj
    rwa [rlc_mem_fourTraceWallGraph_edgeSet_iff gamma gamma' hlat] at hwall
  · rintro ⟨hfg, htrace⟩
    refine ⟨hfg, ?_⟩
    have hlat : sharedPrimalEdge f g ∈ (hypercubicLattice 2).edgeSet := by
      obtain ⟨u, v, huv, huvAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
      rw [huv, SimpleGraph.mem_edgeSet]
      exact huvAdj
    rwa [rlc_mem_fourTraceWallGraph_edgeSet_iff gamma gamma' hlat]


end
end StatMech.Universality
