/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_openSub_axisGapFiniteGraph_restrict_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    FK.openSub (rlc_axisGapFiniteGraph G)
        (rlc_connectorRestrictConfig omega) =
      openSubgraphInduce 2
        (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n) := by
  ext x y
  rw [FK.openSub_adj, openSubgraphInduce_adj, openSubgraph_adj]
  constructor
  · rintro ⟨⟨hadj, hedge⟩, hopen⟩
    refine ⟨hadj, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen
  · rintro ⟨hadj, hopen⟩
    have hedge : s((x : Site 2), (y : Site 2)) ∈ rlc_axisGapEdges G := by
      by_contra hedge
      simp [rlc_maskConfig, hedge] at hopen
    refine ⟨⟨hadj, hedge⟩, ?_⟩
    simpa [rlc_maskConfig, hedge, rlc_connectorRestrictConfig,
      Sym2.map_mk] using hopen


end
end StatMech.Universality
