/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part30
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_sourceBad_exclusiveReflectedLeft_traceResidue_or_otherLocation
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hsourceBad : ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
      gamma gamma' f g) :
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (p ∈ rlc_pathVertices gamma.1 ∨
          (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
              gamma gamma' p ∧
            RlcTwoChannelFullPhysicalExclusiveReflectedLeftSourceTraceResidue
              gamma gamma' omega p q) ∨
          (p 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1,
            p = rlc_flipX w) ∨
          p 0 = -2 * n ∨ p 0 = 2 * n ∨
          p 1 = -n ∨ p 1 = n) := by
  have hnotPlanar : sharedPrimalEdge f g ∉
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    intro hplanar
    exact hsourceBad
      (rlc_twoChannelFullPhysical_sourceCarrier_of_planar
        gamma gamma' omega hfg hplanar)
  obtain ⟨p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩ :=
    rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
      gamma gamma' omega hfg hnotPlanar
  refine ⟨p, q, hpq, hpqAdj, hpReach, hqOut, ?_⟩
  rcases hpPlace with hpBarrier | hpBoundary
  · rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' hpBarrier with
      hpRight | hpLeft | hpFlipLeft | hpFlipRight
    · exact Or.inl hpRight
    · exact False.elim
        ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
          gamma gamma' omega hno hpLeft) hpReach)
    · by_cases hpRight : p ∈ rlc_pathVertices gamma.1
      · exact Or.inl hpRight
      · have hpNotLeft : p ∉ rlc_pathVertices gamma'.1 := by
          intro hpLeft
          have hpLeftBox := rlc_pathVertex_mem_rect gamma'.1 hpLeft
          rw [mem_rect] at hpLeftBox
          omega
        have hpExclusive :
            RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
              gamma gamma' p :=
          ⟨hpFlipLeft.1, hpFlipLeft.2, hpRight, hpNotLeft⟩
        by_cases hpBoundary : p 0 = -2 * n ∨ p 0 = 2 * n ∨
            p 1 = -n ∨ p 1 = n
        · exact Or.inr (Or.inr (Or.inr hpBoundary))
        · have hpBox := rlc_twoChannelFullReachSet_subset_box
            gamma gamma' omega hpReach
          have hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
              -n < p 1 ∧ p 1 < n := by
            rw [mem_rect] at hpBox
            push Not at hpBoundary
            omega
          have hqBox : q ∈ rlc_connectorBox n := by
            simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
            rw [mem_rect]
            have hpqCoord := hpqAdj
            rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqCoord
            omega
          have hpAnchor :
              p ≠ (rlc_connectorRightAnchor gamma : Site 2) := by
            intro hpEq
            have haxis : ((rlc_connectorRightAnchor gamma :
                RlcConnectorVertex n) : Site 2) 0 = 0 := gamma.1.1.2.2
            rw [hpEq] at hpFlipLeft
            omega
          have hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
              s(p, q) = false := by
            have hopen := rlc_twoChannelFullFilledBoundary_le_openFaceDual
              gamma gamma' omega hfg
            rw [openSubgraph_adj] at hopen
            have h := hopen.2
            rw [fci_faceDualConfig,
              fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq] at h
            simpa using h
          rcases
              rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_sourceTraceCross
                gamma gamma' omega hpReach hpInterior hpExclusive hqBox
                  hpqAdj hpAnchor hpqClosed with
            hplanar | htrace
          · exact False.elim (hsourceBad
              (rlc_twoChannelFullPhysical_sourceCarrier_of_planar
                gamma gamma' omega hfg (by simpa [hpq] using hplanar)))
          · exact Or.inr (Or.inl ⟨hpExclusive, htrace⟩)
    · exact Or.inr (Or.inr (Or.inl hpFlipRight))
  · exact Or.inr (Or.inr (Or.inr hpBoundary))


end
end StatMech.Universality
