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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part40
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCollaredWallEdges_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_pimsEdgeEquiv e ∈
      rlc_connectorCollaredWallEdges gamma gamma' := by
  rw [rlc_connectorCollaredWallEdges]
  exact Finset.mem_union_right _
    (rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages
      gamma gamma' htarget hsource htrace)


theorem rlc_connectorCollaredWall_endpoint_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCollaredWallEdges gamma gamma')
    {x : Site 2} (hx : x ∈ e) :
    x ∈ rlc_connectorCollaredSites gamma gamma' := by
  rw [rlc_connectorCollaredSites, Finset.mem_union]
  right
  rw [Finset.mem_biUnion]
  exact ⟨e, he, Sym2.mem_toFinset.mpr hx⟩


theorem rlc_connectorCollaredWallGraph_has_preimage {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (htarget : e ∈ rlc_connectorEdges gamma gamma')
    (htargetLat : e ∈ (hypercubicLattice 2).edgeSet)
    (hsource : rlc_pimsEdgeEquiv e ∉ rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    ∃ x y : RlcConnectorCollaredVertex gamma gamma',
      s(x.1, y.1) = rlc_pimsEdgeEquiv e ∧
        (rlc_connectorCollaredWallGraph gamma gamma').Adj x y := by
  have hwall := rlc_connectorCollaredWallEdges_preimage
    gamma gamma' htarget hsource htrace
  have hlat := rlc_pimsEdgeEquiv_mem_latticeEdge
    htargetLat
  induction hedge : rlc_pimsEdgeEquiv e using Sym2.inductionOn with
  | _ u v =>
    have hu : u ∈ rlc_pimsEdgeEquiv e := by rw [hedge]; simp
    have hv : v ∈ rlc_pimsEdgeEquiv e := by rw [hedge]; simp
    let x : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨u, rlc_connectorCollaredWall_endpoint_mem gamma gamma' hwall hu⟩
    let y : RlcConnectorCollaredVertex gamma gamma' :=
      ⟨v, rlc_connectorCollaredWall_endpoint_mem gamma gamma' hwall hv⟩
    refine ⟨x, y, ?_, ?_⟩
    · simp [x, y]
    · refine ⟨?_, ?_⟩
      · rw [← SimpleGraph.mem_edgeSet, ← hedge]
        exact hlat
      · simpa [x, y, hedge] using hwall


theorem rlc_extremalSelection_bad_preimage_is_collaredWall :
    ∃ x y : RlcConnectorCollaredVertex
        rlc_traceSplitCounterexampleRight
        rlc_traceSplitCounterexampleLeft,
      s(x.1, y.1) = rlc_pimsEdgeEquiv
          s(rlc_extremalSelectionExteriorBadX.1,
            rlc_extremalSelectionExteriorBadY.1) ∧
        (rlc_connectorCollaredWallGraph
          rlc_traceSplitCounterexampleRight
          rlc_traceSplitCounterexampleLeft).Adj x y := by
  apply rlc_connectorCollaredWallGraph_has_preimage
  · exact rlc_extremalSelection_bad_target_mem_connectorEdges
  · simp [rlc_extremalSelectionExteriorBadX,
      rlc_extremalSelectionExteriorBadY, hypercubicLattice_adj,
      Fin.sum_univ_two]
  · simpa [rlc_extremalSelectionExteriorBadX,
      rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
      rlc_pimsEdgeEquiv_horizontal] using
        rlc_extremalSelection_bad_source_not_connectorEdges
  · simpa [rlc_extremalSelectionExteriorBadX,
      rlc_extremalSelectionExteriorBadY, Sym2.map_mk,
      rlc_pimsEdgeEquiv_horizontal] using
        rlc_extremalSelection_bad_source_not_traceEdges

end
end StatMech.Universality
