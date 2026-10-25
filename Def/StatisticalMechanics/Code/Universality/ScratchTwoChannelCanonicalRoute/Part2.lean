/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelPIMSSourceEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
  let sourceSite := rlc_pimsEdgeEquiv (target.1.1.map Subtype.val)
  let sourceLift := rlc_connectorCentralFaceEdgeLift sourceSite target.2
  have hlat : sourceSite ∈ (hypercubicLattice 2).edgeSet :=
    rlc_pimsEdgeEquiv_mem_latticeEdge
      (rlc_twoChannelEdge_site_mem_lattice target.1)
  have hcentral : sourceLift ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet :=
    rlc_centralFaceEdgeLift_mem_graph sourceSite target.2 hlat
  exact ⟨sourceLift, SimpleGraph.edgeSet_mono
    (rlc_connectorCentralFaceFiniteGraph_le_twoChannel gamma gamma')
      hcentral⟩

end
end StatMech.Universality
