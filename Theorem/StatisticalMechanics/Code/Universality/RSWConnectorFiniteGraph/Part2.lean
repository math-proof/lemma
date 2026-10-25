/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_openSub_connectorFiniteGraph_restrict_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    FK.openSub (rlc_connectorFiniteGraph gamma gamma')
        (rlc_connectorRestrictConfig omega) =
      openSubgraphInduce 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 * n) (2 * n) (-n) n) := by
  ext x y
  rw [FK.openSub_adj, openSubgraphInduce_adj, openSubgraph_adj]
  constructor
  · rintro ⟨⟨hadj, hedge⟩, hopen⟩
    refine ⟨hadj, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen
  · rintro ⟨hadj, hopen⟩
    have hedge : s((x : Site 2), (y : Site 2)) ∈
        rlc_connectorEdges gamma gamma' := by
      by_contra hedge
      simp [rlc_maskConfig, hedge] at hopen
    refine ⟨⟨hadj, hedge⟩, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen


end
end StatMech.Universality
