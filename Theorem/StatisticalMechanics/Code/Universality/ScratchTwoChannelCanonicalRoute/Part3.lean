/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelEdge_site_mem_lattice {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    e.1.map Subtype.val ∈ (hypercubicLattice 2).edgeSet := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact he.1.elim (fun h => h.1) (fun h => h.1)

theorem rlc_centralFaceEdgeLift_mem_graph {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : Sym2 (Site 2))
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    rlc_connectorCentralFaceEdgeLift e he ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet := by
  let lift := rlc_connectorCentralFaceEdgeLift e he
  change lift ∈
    (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet
  induction hlift : lift using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      have hmap := rlc_connectorCentralFaceEdgeLift_map e he
      change lift.map Subtype.val = e at hmap
      rw [hlift, Sym2.map_mk] at hmap
      have hlat' : s((x : Site 2), (y : Site 2)) ∈
          (hypercubicLattice 2).edgeSet := by simpa [hmap] using hlat
      exact ⟨(SimpleGraph.mem_edgeSet _).mp hlat', by simpa [hmap] using he⟩


end
end StatMech.Universality
