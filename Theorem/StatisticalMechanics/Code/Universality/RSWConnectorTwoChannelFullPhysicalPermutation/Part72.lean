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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part71
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_finiteBidirectionalStrictRankTransition_twoCycle :
    ∃ (states : Finset Nat) (next : Nat → Nat),
      RlcFiniteBidirectionalStrictRankTransition states id next ∧
        0 ∈ states ∧ next 0 ≠ 0 ∧ next (next 0) = 0 := by
  let next : Nat → Nat := fun z => if z = 0 then 1 else 0
  refine ⟨{0, 1}, next, ?_, by simp, by simp [next], by simp [next]⟩
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · simp [next]
  · simp [next]


theorem rlc_twoChannelFullPhysical_maxOrderedIntersection_twoArcNoGood_of_noGood
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    ∃ (z x y u : Site 2)
      (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
      (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
      (hx : x ∈ c.support) (hy : y ∈ c.support),
      c.IsCycle ∧
        z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z) ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        rlc_flipX (rlc_dualReflect x) ∈
          (right.map rlc_flipXLatticeHom).support ∧
        rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
        RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
        RlcBookRightIntersectionRankRealizedAt gamma right ∧
        RlcBookRightPrefixRankAt gamma right ∧
        RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
          gamma gamma' omega c hx hy ∧
        ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
        ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
  obtain ⟨z, hzCandidate, hzMax⟩ :=
    rlc_exists_max_bookOrderedIntersectionCandidate gamma gamma' hfaith
  have hzIntersection := (Finset.mem_filter.mp hzCandidate).1
  have hzMem := Finset.mem_filter.mp hzIntersection
  obtain ⟨x, y, right, flipLeft, hxSupport, hySupport, hxPath, hyPath,
      hxOrder, hyOrder, hflipLeftRank, hrightRank, hrightPrefix⟩ :=
    rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
      gamma gamma' hfaith omega hno z hzMem.1 hzMem.2
  obtain ⟨u, c, hcycle, hx, hy⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts
      gamma gamma' omega hxSupport hySupport
  have hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy := by
    intro hside
    exact hnoGood
      (rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide
        gamma gamma' omega c hx hy hxPath hyPath hside)
  obtain ⟨hclassified, hxPlace, hyPlace⟩ :=
    rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad
      hfaith omega c hcycle.isTrail hx hy hxPath hyPath hbadSide
  have hbad :=
    rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified
      hno hnoGood c hx hy hxPath hyPath hclassified
  exact ⟨z, x, y, u, right, flipLeft, c, hx, hy, hcycle,
    hzCandidate, hzMax, hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank,
    hrightRank, hrightPrefix, hbad, hxPlace, hyPlace⟩


theorem rlc_twoChannelFullPhysical_minOrderedIntersection_twoArcNoGood_of_noGood
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    ∃ (z x y u : Site 2)
      (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
      (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
      (hx : x ∈ c.support) (hy : y ∈ c.support),
      c.IsCycle ∧
        z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        rlc_flipX (rlc_dualReflect x) ∈
          (right.map rlc_flipXLatticeHom).support ∧
        rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
        RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
        RlcBookRightIntersectionRankRealizedAt gamma right ∧
        RlcBookRightPrefixRankAt gamma right ∧
        RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
          gamma gamma' omega c hx hy ∧
        ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
        ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
  obtain ⟨z, hzCandidate, hzMin⟩ :=
    rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith
  have hzIntersection := (Finset.mem_filter.mp hzCandidate).1
  have hzMem := Finset.mem_filter.mp hzIntersection
  obtain ⟨x, y, right, flipLeft, hxSupport, hySupport, hxPath, hyPath,
      hxOrder, hyOrder, hflipLeftRank, hrightRank, hrightPrefix⟩ :=
    rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
      gamma gamma' hfaith omega hno z hzMem.1 hzMem.2
  obtain ⟨u, c, hcycle, hx, hy⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts
      gamma gamma' omega hxSupport hySupport
  have hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy := by
    intro hside
    exact hnoGood
      (rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide
        gamma gamma' omega c hx hy hxPath hyPath hside)
  obtain ⟨hclassified, hxPlace, hyPlace⟩ :=
    rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad
      hfaith omega c hcycle.isTrail hx hy hxPath hyPath hbadSide
  have hbad :=
    rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified
      hno hnoGood c hx hy hxPath hyPath hclassified
  exact ⟨z, x, y, u, right, flipLeft, c, hx, hy, hcycle,
    hzCandidate, hzMin, hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank,
    hrightRank, hrightPrefix, hbad, hxPlace, hyPlace⟩


theorem rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hside : RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
  rcases hside with hordered | hcomplementary
  · refine ⟨x, y, rlc_orderedContourArc c hx hy,
      hxPath, hyPath, ?_⟩
    intro e he
    induction e using Sym2.inductionOn with
    | _ f g =>
        have hfg :=
          (rlc_orderedContourArc c hx hy).adj_of_mem_edges he
        exact
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨hfg, hordered he⟩).2
  · refine ⟨x, y, rlc_complementaryContourArc c hx hy,
      hxPath, hyPath, ?_⟩
    intro e he
    induction e using Sym2.inductionOn with
    | _ f g =>
        have hfg :=
          (rlc_complementaryContourArc c hx hy).adj_of_mem_edges he
        exact
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨hfg, hcomplementary he⟩).2


end
end StatMech.Universality
