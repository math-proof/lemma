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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part32
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalSourceResidue_rightTrace_or_boxWall
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hsource : RlcTwoChannelFullPhysicalReflectedLeftTerminalSourceResidue
      gamma gamma' omega f g) :
    (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧
      ∃ p q : Site 2,
        sharedPrimalEdge f g = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' p ∧
            RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
              gamma gamma' omega p q) ∨
            p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) := by
  rcases hsource with
    ⟨hsourceBad, p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩
  refine ⟨hsourceBad, p, q, hpq, hpqAdj, hpReach, hqOut, ?_⟩
  have hpBounds : f 0 ≤ p 0 ∧ p 0 ≤ f 0 + 1 := by
    rcases face_adj_dir hfg.1 with hg | hg | hg | hg
    · subst g
      rw [show sharedPrimalEdge f ![f 0 + 1, f 1] =
          s(![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1]) by
            simpa using sharedPrimalEdge_right (f 0) (f 1),
        Sym2.eq_iff] at hpq
      rcases hpq with h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp
    · subst g
      rw [show sharedPrimalEdge f ![f 0 - 1, f 1] =
          s(faceCorner00 (f 0) (f 1), faceCorner01 (f 0) (f 1)) by
            simpa using sharedPrimalEdge_left (f 0) (f 1),
        Sym2.eq_iff] at hpq
      rcases hpq with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
        simp [faceCorner00, faceCorner01]
    · subst g
      rw [show sharedPrimalEdge f ![f 0, f 1 + 1] =
          s(![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1]) by
            simpa using sharedPrimalEdge_top (f 0) (f 1),
        Sym2.eq_iff] at hpq
      rcases hpq with h | h <;> rcases h with ⟨rfl, rfl⟩ <;> simp
    · subst g
      rw [show sharedPrimalEdge f ![f 0, f 1 - 1] =
          s(faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1)) by
            simpa using sharedPrimalEdge_bottom (f 0) (f 1),
        Sym2.eq_iff] at hpq
      rcases hpq with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
        simp [faceCorner00, faceCorner10]
  have hfPos := hfExclusive.1
  have hpNeg : p 0 < 0 := by
    simp [rlc_dualReflect, rlc_dualReflectFun] at hfPos
    omega
  rcases hpPlace with hpRight | hpLeft | hpFlipRight | hpBoundary
  · have hpRect := rlc_pathVertex_mem_rect gamma.1 hpRight
    rw [mem_rect] at hpRect
    omega
  · exact False.elim (by
      have hpPos := hpLeft.1.1
      omega)
  · have hpNotRight : p ∉ rlc_pathVertices gamma.1 := by
      intro hpRight
      have hpRect := rlc_pathVertex_mem_rect gamma.1 hpRight
      rw [mem_rect] at hpRect
      omega
    have hpNotLeft : p ∉ rlc_pathVertices gamma'.1 := by
      intro hpLeft
      exact (rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
        gamma gamma' omega hno hpLeft) hpReach
    have hpExclusive :
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' p :=
      ⟨hpFlipRight.1, hpFlipRight.2, hpNotRight, hpNotLeft⟩
    by_cases hpBoundary : p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n
    · exact Or.inr hpBoundary
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
        rw [hpEq] at hpNeg
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
          rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_sourceTraceCross
            gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj
              hpAnchor hpqClosed with
        hplanar | htrace
      · exact False.elim (hsourceBad
          (rlc_twoChannelFullPhysical_sourceCarrier_of_planar
            gamma gamma' omega hfg (by simpa [hpq] using hplanar)))
      · exact Or.inl ⟨hpExclusive, htrace⟩
  · rcases hpBoundary with hpLeft | hpRight | hpBottom | hpTop
    · exact Or.inr (Or.inl hpLeft)
    · exact False.elim (by omega)
    · exact Or.inr (Or.inr (Or.inl hpBottom))
    · exact Or.inr (Or.inr (Or.inr hpTop))


end
end StatMech.Universality
