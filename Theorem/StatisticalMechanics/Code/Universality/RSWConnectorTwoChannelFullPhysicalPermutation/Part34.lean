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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part34
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_goodComponent_or_classifiedBadSeparation
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
      RlcTwoChannelFullPhysicalClassifiedBadCarrierSeparation
        gamma gamma' omega := by
  rcases rlc_twoChannelFullPhysical_goodComponent_or_badCarrierSeparation
      gamma gamma' hfaith omega hno with hgood | hbad
  · exact Or.inl hgood
  · right
    obtain ⟨x, y, u, v, hxPath, hyPath, hxu, huv, huvBad, hvy⟩ := hbad
    have hxBarrier : rlc_dualReflect x ∈
        rlc_connectorBarrier gamma gamma' := by
      simp [rlc_connectorBarrier, hxPath]
    have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
      simpa [rlc_connectorBox] using
        (rlc_rightPathVertex_mem_connectorBox gamma hxPath)
    have hclass :
        ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
              gamma gamma' u v) ∧
            (rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
              (rlc_dualReflect u) 0 = -2 * n ∨
              (rlc_dualReflect u) 0 = 2 * n ∨
              (rlc_dualReflect u) 1 = -n ∨
              (rlc_dualReflect u) 1 = n)) ∨
          ∃ p q : Site 2,
            sharedPrimalEdge u v = s(p, q) ∧
              (hypercubicLattice 2).Adj p q ∧
              p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
              q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
              (p ∈ rlc_connectorBarrier gamma gamma' ∨
                p 0 = -2 * n ∨ p 0 = 2 * n ∨
                p 1 = -n ∨ p 1 = n) := by
      rcases rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
          gamma gamma' omega huv huvBad with htarget | hsource
      · exact Or.inl ⟨htarget,
          rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
            hxBarrier hxBox hxu.some huv htarget⟩
      · exact Or.inr
          (rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
            gamma gamma' omega huv hsource)
    exact ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hvy, hclass⟩


theorem rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    (H : Set (Site 2)) {u z : Site 2}
    (p : (hypercubicLattice 2).Walk (rlc_flipX u) (rlc_flipX z))
    (hpTrace : ∀ v ∈ p.support,
      ∃ w ∈ rlc_pathVertices tau, rlc_flipX w = v)
    (huIn : rlc_flipX u ∈ H) (hzOut : rlc_flipX z ∉ H) :
    ∃ x : Site 2,
      x ∈ (faceBoundaryGraph H).support ∧
        rlc_dualReflect x ∈ rlc_pathVertices tau ∧
        rlc_flipX (rlc_dualReflect x) ∈ p.support := by
  obtain ⟨r, s, hrsBoundary, hrsEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges H p huIn hzOut
  have hrSupport : r ∈ p.support := p.fst_mem_support_of_mem_edges hrsEdge
  have hsSupport : s ∈ p.support := p.snd_mem_support_of_mem_edges hrsEdge
  obtain ⟨r0, hr0Path, hr0Eq⟩ := hpTrace r hrSupport
  obtain ⟨s0, hs0Path, hs0Eq⟩ := hpTrace s hsSupport
  have hflankEdge : flankFaces r s ∈ (faceBoundaryGraph H).edgeSet := by
    rw [phb_flankFaces_mem_faceBoundaryGraph_iff hrsBoundary.1,
      bdEdge_mk]
    exact hrsBoundary.2
  obtain ⟨f, g, hflank, hfgLat⟩ := flankFaces_latAdj hrsBoundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    rw [← SimpleGraph.mem_edgeSet, ← hflank]
    exact hflankEdge
  rcases rlc_doubleDualShift_endpoint_mem_flankFaces hrsBoundary.1 with
      hrShift | hsShift
  · rw [hflank, Sym2.mem_iff] at hrShift
    rcases hrShift with hrShift | hrShift
    · refine ⟨f, hfg.mem_support_left, ?_, ?_⟩
      · have hrf : phb_doubleDualShift (rlc_flipX r0) = f := by
          rw [hr0Eq]
          exact hrShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrf
        rw [← hrf]
        simpa using hr0Path
      · have hrf : phb_doubleDualShift (rlc_flipX r0) = f := by
          rw [hr0Eq]
          exact hrShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrf
        simpa [← hrf, hr0Eq] using hrSupport
    · refine ⟨g, hfg.mem_support_right, ?_, ?_⟩
      · have hrg : phb_doubleDualShift (rlc_flipX r0) = g := by
          rw [hr0Eq]
          exact hrShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrg
        rw [← hrg]
        simpa using hr0Path
      · have hrg : phb_doubleDualShift (rlc_flipX r0) = g := by
          rw [hr0Eq]
          exact hrShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrg
        simpa [← hrg, hr0Eq] using hrSupport
  · rw [hflank, Sym2.mem_iff] at hsShift
    rcases hsShift with hsShift | hsShift
    · refine ⟨f, hfg.mem_support_left, ?_, ?_⟩
      · have hsf : phb_doubleDualShift (rlc_flipX s0) = f := by
          rw [hs0Eq]
          exact hsShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hsf
        rw [← hsf]
        simpa using hs0Path
      · have hsf : phb_doubleDualShift (rlc_flipX s0) = f := by
          rw [hs0Eq]
          exact hsShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hsf
        simpa [← hsf, hs0Eq] using hsSupport
    · refine ⟨g, hfg.mem_support_right, ?_, ?_⟩
      · have hsg : phb_doubleDualShift (rlc_flipX s0) = g := by
          rw [hs0Eq]
          exact hsShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hsg
        rw [← hsg]
        simpa using hs0Path
      · have hsg : phb_doubleDualShift (rlc_flipX s0) = g := by
          rw [hs0Eq]
          exact hsShift
        rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hsg
        simpa [← hsg, hs0Eq] using hsSupport


theorem rlc_exists_last_bookFlippedTraceIntersection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ z : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
      ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
        rlc_bookFlippedTraceIntersectionRank gamma gamma' q ≤
          rlc_bookFlippedTraceIntersectionRank gamma gamma' z := by
  classical
  have hne := rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful
    gamma gamma' hfaith
  letI : Nonempty ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma')).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmax⟩ := Finset.exists_max_image
    (Finset.univ :
      Finset ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'))
    (rlc_bookFlippedTraceIntersectionRank gamma gamma') huniv
  exact ⟨z, fun q => hmax q (by simp)⟩


theorem rlc_bookLastFlippedTraceIntersection_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (z : Site 2)
      (hz : z ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma'),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
          rlc_bookFlippedTraceIntersectionRank gamma gamma' q ≤
            rlc_bookFlippedTraceIntersectionRank gamma gamma'
              ⟨z, hz⟩ := by
  classical
  obtain ⟨zs, hmax⟩ :=
    rlc_exists_last_bookFlippedTraceIntersection gamma gamma' hfaith
  have hzMem := Finset.mem_filter.mp zs.2
  exact ⟨zs.1, zs.2, hzMem.1, hzMem.2, hmax⟩


end
end StatMech.Universality
