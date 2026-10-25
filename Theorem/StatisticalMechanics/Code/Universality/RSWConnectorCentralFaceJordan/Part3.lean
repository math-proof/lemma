/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_centralFaceContactSubwalk_edges_subset
    {H : SimpleGraph (Site 2)} {f g x y : Site 2} (a : H.Walk f g)
    (hx : x ∈ a.support) (hy : y ∈ a.support) :
    ∀ e ∈ (rlc_centralFaceContactSubwalk a hx hy).edges, e ∈ a.edges := by
  intro e he
  rw [rlc_centralFaceContactSubwalk,
    SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
    List.mem_append] at he
  rcases he with he | he
  · exact a.edges_takeUntil_subset hx (by simpa using he)
  · exact a.edges_takeUntil_subset hy he


theorem rlc_connectorCentralFaceReachSet_edgeBoundary_closed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)) :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho
  · have hw : w ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho := hsplit.mp hv
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges
      gamma gamma' rho hopen
    have hwBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right v w)
    exact hw (rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hv
      (by simpa [rlc_connectorBox] using hwBox) hadj hopen)
  · have hw : w ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_connectorCentralFaceAmbientConfig_open_mem_planarEdges
      gamma gamma' rho hopen
    have hvBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right w v)
    exact hv (rlc_connectorCentralFaceReachSet_extend gamma gamma' rho hw
      (by simpa [rlc_connectorBox] using hvBox) hadj.symm hopen)


theorem rlc_connectorCentralFaceBoundary_le_openFaceDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    faceBoundaryGraph (rlc_connectorCentralFaceReachSet gamma gamma' rho) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorCentralFaceReachSet gamma gamma' rho) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_connectorCentralFaceReachSet_edgeBoundary_closed
    gamma gamma' rho hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed


end
end StatMech.Universality
