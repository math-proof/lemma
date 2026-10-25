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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part37
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_not_cyclicOrderCrossingCertificate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (C : RlcTwoChannelFullPhysicalCyclicOrderCrossingCertificate
      gamma gamma' omega) : False := by
  let V := C.arc.mapLe
    (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
  have hVBox : ∀ z ∈ V.support,
      z ∈ rect C.alpha C.beta C.bottom C.top := by
    intro z hz
    apply C.arc_mem_box z
    simpa [V, SimpleGraph.Walk.support_mapLe_eq_support] using hz
  have hpre : ∀ z ∈ C.trace.support,
      z ∈ (sw_vertSeg (C.x 0) C.bottom (C.x 1)).support →
        z ∈ V.support := by
    intro z hzTrace hzCollar
    simpa [V, SimpleGraph.Walk.support_mapLe_eq_support] using
      C.lower_collar_contact z hzTrace hzCollar
  have hpost : ∀ z ∈ C.trace.support,
      z ∈ (sw_vertSeg (C.y 0) (C.y 1) C.top).support →
        z ∈ V.support := by
    intro z hzTrace hzCollar
    simpa [V, SimpleGraph.Walk.support_mapLe_eq_support] using
      C.upper_collar_contact z hzTrace hzCollar
  obtain ⟨z, hzTrace, hzV⟩ :=
    rlc_collaredVerticalArc_meets_leftRightWalk
      C.alpha_lt_beta C.bottom_le_top C.x_mem_box C.y_mem_box
        V hVBox C.trace C.traceStart_mem_box C.traceEnd_mem_box
          C.traceStart_left C.traceEnd_right C.trace_mem_box hpre hpost
  apply C.trace_disjoint_arc z hzTrace
  simpa [V, SimpleGraph.Walk.support_mapLe_eq_support] using hzV


theorem rlc_bookRightIntersectionRank_strict_of_ne {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {z r : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hrRight : r ∈ rlc_pathVertices gamma.1)
    (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
    (hrz : r ≠ z) :
    right.length < (rlc_ambientCrossingWalk gamma.1).support.idxOf r := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
      hzRight
  have hrW : r ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2
      hrRight
  have hle : right.length ≤ W.support.idxOf r := by
    simpa [W] using hmin r hrRight hrLeft
  have hne : right.length ≠ W.support.idxOf r := by
    intro heq
    apply hrz
    have hrank' : right.length = W.support.idxOf z := by
      simpa [RlcBookRightIntersectionRankRealizedAt, W] using hrank
    have hidx : W.support.idxOf z = W.support.idxOf r :=
      hrank'.symm.trans heq
    exact ((List.idxOf_inj hzW).1 hidx).symm
  change right.length < W.support.idxOf r
  omega


theorem rlc_twoChannelFullPhysical_leftContact_reflectedRight_rank_progress
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z y u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y u)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (huRight : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX r) :
    ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX r ∧
        r ∈ flipLeft.support ∧
        (r = z ∨
          right.length <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf r) := by
  obtain ⟨r, hrRight, hyr⟩ :=
    rlc_twoChannelFullPhysical_reflectedRightWalk_start q hedges huRight
  have hrSuffix : r ∈ flipLeft.support := by
    rw [hyr] at hyOrder
    simpa using hyOrder
  have hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1 := by
    rw [hyr] at hyLeft
    simpa using hyLeft
  refine ⟨r, hrRight, hyr, hrSuffix, ?_⟩
  by_cases hrz : r = z
  · exact Or.inl hrz
  · exact Or.inr
      (rlc_bookRightIntersectionRank_strict_of_ne
        right hzRight hrRight hrLeft hrank hmin hrz)


theorem RlcBookFaithfulTracePair.intersection_ne_flip {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    z ≠ rlc_flipX z := by
  intro hzFlip
  have hz0 : z 0 = 0 := by
    have h0 := congrArg (fun w : Site 2 => w 0) hzFlip
    change z 0 = -z 0 at h0
    omega
  have hzRightAxis := hfaith.right_axis_unique hzRight hz0
  have hzLeft' : z ∈ rlc_pathVertices gamma'.1 := by
    simpa [← hzFlip] using hzLeft
  have hzLeftAxis := hfaith.left_axis_unique hzLeft' hz0
  have hcontacts : (gamma.1.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) := hzRightAxis.symm.trans hzLeftAxis
  have hheight := congrArg (fun w : Site 2 => w 1) hcontacts
  exact (ne_of_lt hfaith.axis_contacts_strict) hheight


theorem RlcBookFaithfulTracePair.intersection_positive {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    0 < z 0 := by
  apply hfaith.right_vertex_strict hzRight
  intro hzStart
  apply hfaith.intersection_ne_flip hzRight hzLeft
  rw [hzStart]
  exact (rlc_flipX_eq_self_of_zero gamma.1.1.2.2).symm


end
end StatMech.Universality
