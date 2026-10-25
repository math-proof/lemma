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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part41
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_bookOrderedCandidateReverseRank_lt_of_rightRank_lt
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {z q : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hqCandidate : q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzq : (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q) :
    rlc_bookOrderedCandidateReverseRank gamma q <
      rlc_bookOrderedCandidateReverseRank gamma z := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hzPath :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hzCandidate).1).1
  have hqPath :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hqCandidate).1).1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
      hzPath
  have hqW : q ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2
      hqPath
  have hzLt := List.idxOf_lt_length_of_mem hzW
  have hqLt := List.idxOf_lt_length_of_mem hqW
  rw [SimpleGraph.Walk.length_support] at hzLt hqLt
  have hzqW : W.support.idxOf z < W.support.idxOf q := by
    simpa [W] using hzq
  simp only [rlc_bookOrderedCandidateReverseRank]
  change W.length - W.support.idxOf q < W.length - W.support.idxOf z
  omega


theorem rlc_bookFirstIntersection_mem_orderedCandidateSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right) :
    z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' := by
  classical
  rw [rlc_bookOrderedIntersectionCandidateSet, Finset.mem_filter]
  constructor
  · simp [rlc_bookFlippedTraceIntersectionSet, hzRight, hzLeft]
  · intro q hq hqBefore _hzBeforeQ
    have hqMem := Finset.mem_filter.mp hq
    have hqAfter := hmin q hqMem.1 hqMem.2
    have hrank' : right.length =
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z := hrank
    have hidx : (rlc_ambientCrossingWalk gamma.1).support.idxOf q =
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by
      omega
    have hzW : z ∈ (rlc_ambientCrossingWalk gamma.1).support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
        hzRight
    exact ((List.idxOf_inj hzW).1 hidx.symm).symm


theorem rlc_bookOrderedIntersectionCandidate_rightRank_strict
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z r : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
    (hzrLeft :
      (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
        (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX r))
    (hrz : r ≠ z) :
    (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
      (rlc_ambientCrossingWalk gamma.1).support.idxOf r := by
  classical
  have hrecord := (Finset.mem_filter.mp hzCandidate).2
  by_contra hnot
  have hrBefore :
      (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by omega
  exact hrz (hrecord r hrSet hrBefore hzrLeft)


theorem rlc_bookOrderedIntersectionCandidates_order_agree
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z q : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hqCandidate : q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
    ((rlc_ambientCrossingWalk gamma.1).support.idxOf q <
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z) ↔
      ((rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX q) <
        (rlc_ambientCrossingWalk gamma'.1).support.idxOf
          (rlc_flipX z)) := by
  classical
  have hzSet := (Finset.mem_filter.mp hzCandidate).1
  have hqSet := (Finset.mem_filter.mp hqCandidate).1
  have hzRecord := (Finset.mem_filter.mp hzCandidate).2
  have hqRecord := (Finset.mem_filter.mp hqCandidate).2
  constructor
  · intro hqz
    by_contra hnot
    have hzqLeft :
        (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
          (rlc_ambientCrossingWalk gamma'.1).support.idxOf
            (rlc_flipX q) := by omega
    have hqzEq := hzRecord q hqSet (by omega) hzqLeft
    subst q
    simp at hqz
  · intro hqz
    by_contra hnot
    have hzqRight : (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by omega
    have hqzEq := hqRecord z hzSet hzqRight (by omega)
    subst q
    simp at hqz


theorem rlc_bookOrderedIntersectionCandidate_exists_later
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z r : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
    (hzrLeft :
      (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
        (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX r))
    (hrz : r ≠ z) :
    ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf r := by
  classical
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  let S := (rlc_bookFlippedTraceIntersectionSet gamma gamma').filter fun q =>
    WR.support.idxOf z < WR.support.idxOf q ∧
      WL.support.idxOf (rlc_flipX z) ≤
        WL.support.idxOf (rlc_flipX q)
  have hrLater := rlc_bookOrderedIntersectionCandidate_rightRank_strict
    hzCandidate hrSet hzrLeft hrz
  have hrS : r ∈ S := by
    exact Finset.mem_filter.mpr ⟨hrSet, hrLater, hzrLeft⟩
  obtain ⟨q, hqS, hqMin⟩ := Finset.exists_min_image S
    (fun w => WR.support.idxOf w) ⟨r, hrS⟩
  have hqInfo := Finset.mem_filter.mp hqS
  have hzRecord := (Finset.mem_filter.mp hzCandidate).2
  have hqCandidate : q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma' := by
    rw [rlc_bookOrderedIntersectionCandidateSet, Finset.mem_filter]
    refine ⟨hqInfo.1, ?_⟩
    intro s hs hsBefore hqLeftS
    by_cases hsBeforeZ : WR.support.idxOf s ≤ WR.support.idxOf z
    · have hsz := hzRecord s hs hsBeforeZ
        (le_trans hqInfo.2.2 hqLeftS)
      subst s
      have hleftEq : WL.support.idxOf (rlc_flipX z) =
          WL.support.idxOf (rlc_flipX q) :=
        le_antisymm hqInfo.2.2 hqLeftS
      have hzSet := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hzCandidate).1)
      have hzWL : rlc_flipX z ∈ WL.support :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 (rlc_flipX z)).2 hzSet.2
      have hflipEq : rlc_flipX z = rlc_flipX q :=
        (List.idxOf_inj hzWL).1 hleftEq
      exact rlc_flipX.injective hflipEq
    · have hsAfterZ : WR.support.idxOf z < WR.support.idxOf s := by
        omega
      have hsS : s ∈ S := Finset.mem_filter.mpr
        ⟨hs, hsAfterZ, le_trans hqInfo.2.2 hqLeftS⟩
      have hqBeforeS := hqMin s hsS
      have hrightEq : WR.support.idxOf q = WR.support.idxOf s :=
        le_antisymm hqBeforeS hsBefore
      have hqSet := Finset.mem_filter.mp hqInfo.1
      have hqWR : q ∈ WR.support :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2
          hqSet.1
      exact ((List.idxOf_inj hqWR).1 hrightEq).symm
  exact ⟨q, hqCandidate, hqInfo.2.1, hqMin r hrS⟩


theorem rlc_bookOrderedIntersectionCandidate_exists_earlier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z r : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
    (hrzRight :
      (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hrz : r ≠ z) :
    ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by
  classical
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hzInfo := Finset.mem_filter.mp
    (Finset.mem_filter.mp hzCandidate).1
  have hrInfo := Finset.mem_filter.mp hrSet
  have hrzRight' : WR.support.idxOf r ≤ WR.support.idxOf z := by
    simpa [WR] using hrzRight
  have hrzStrict : WR.support.idxOf r < WR.support.idxOf z := by
    by_contra hnot
    have heq : WR.support.idxOf r = WR.support.idxOf z := by
      omega
    have hrW : r ∈ WR.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2
        hrInfo.1
    exact hrz ((List.idxOf_inj hrW).1 heq)
  have hrzLeft : WL.support.idxOf (rlc_flipX r) <
      WL.support.idxOf (rlc_flipX z) := by
    by_contra hnot
    have hzBeforeR : WL.support.idxOf (rlc_flipX z) ≤
        WL.support.idxOf (rlc_flipX r) := by omega
    exact hrz ((Finset.mem_filter.mp hzCandidate).2 r hrSet hrzRight
      (by simpa [WL] using hzBeforeR))
  let S := (rlc_bookFlippedTraceIntersectionSet gamma gamma').filter fun q =>
    WR.support.idxOf q < WR.support.idxOf z ∧
      WL.support.idxOf (rlc_flipX q) < WL.support.idxOf (rlc_flipX z)
  have hrS : r ∈ S := by
    exact Finset.mem_filter.mpr ⟨hrSet, hrzStrict, hrzLeft⟩
  obtain ⟨q, hqS, hqMin⟩ := Finset.exists_min_image S
    (fun w => WR.support.idxOf w) ⟨r, hrS⟩
  have hqInfo := Finset.mem_filter.mp hqS
  have hzRecord := (Finset.mem_filter.mp hzCandidate).2
  have hqCandidate : q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma' := by
    rw [rlc_bookOrderedIntersectionCandidateSet, Finset.mem_filter]
    refine ⟨hqInfo.1, ?_⟩
    intro s hs hsBefore hqLeftS
    have hsBeforeZ : WR.support.idxOf s < WR.support.idxOf z :=
      lt_of_le_of_lt hsBefore hqInfo.2.1
    have hsLeftZ : WL.support.idxOf (rlc_flipX s) <
        WL.support.idxOf (rlc_flipX z) := by
      by_contra hnot
      have hzLeftS : WL.support.idxOf (rlc_flipX z) ≤
          WL.support.idxOf (rlc_flipX s) := by omega
      have hsBeforeZ' :
          (rlc_ambientCrossingWalk gamma.1).support.idxOf s <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by
        simpa [WR] using hsBeforeZ
      have hsz := hzRecord s hs (Nat.le_of_lt hsBeforeZ')
        (by simpa [WL] using hzLeftS)
      subst s
      simp at hsBeforeZ
    have hsS : s ∈ S := Finset.mem_filter.mpr
      ⟨hs, hsBeforeZ, hsLeftZ⟩
    have hqBeforeS := hqMin s hsS
    have hrightEq : WR.support.idxOf q = WR.support.idxOf s :=
      le_antisymm hqBeforeS hsBefore
    have hqSet := Finset.mem_filter.mp hqInfo.1
    have hqWR : q ∈ WR.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2
        hqSet.1
    exact ((List.idxOf_inj hqWR).1 hrightEq).symm
  exact ⟨q, hqCandidate, by simpa [WR] using hqMin r hrS,
    by simpa [WR] using hqInfo.2.1⟩


theorem rlc_exists_max_bookOrderedIntersectionCandidate
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by
  classical
  obtain ⟨z, hzW, hzRight, hzLeft, _hfirst, hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let right := (rlc_ambientCrossingWalk gamma.1).takeUntil z hzW
  have hrank : RlcBookRightIntersectionRankRealizedAt gamma right := by
    simp [RlcBookRightIntersectionRankRealizedAt, right,
      SimpleGraph.Walk.length_takeUntil]
  have hmin : RlcBookRightIntersectionRankMinimalAt
      gamma gamma' right := by
    intro q hqRight hqLeft
    have hqW :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2
        hqRight
    simpa [RlcBookRightIntersectionRankMinimalAt, right,
      SimpleGraph.Walk.length_takeUntil] using hglobalMin q hqW hqLeft
  have hzCandidate := rlc_bookFirstIntersection_mem_orderedCandidateSet
    right hzRight hzLeft hrank hmin
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image
    (rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (fun w => (rlc_ambientCrossingWalk gamma.1).support.idxOf w)
    ⟨z, hzCandidate⟩
  exact ⟨m, hm, fun q hq => hmax q hq⟩


theorem rlc_exists_min_bookOrderedIntersectionCandidate
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
  classical
  obtain ⟨z, hzW, hzRight, hzLeft, _hfirst, hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  let right := (rlc_ambientCrossingWalk gamma.1).takeUntil z hzW
  have hrank : RlcBookRightIntersectionRankRealizedAt gamma right := by
    simp [RlcBookRightIntersectionRankRealizedAt, right,
      SimpleGraph.Walk.length_takeUntil]
  have hmin : RlcBookRightIntersectionRankMinimalAt
      gamma gamma' right := by
    intro q hqRight hqLeft
    have hqW :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2
        hqRight
    simpa [RlcBookRightIntersectionRankMinimalAt, right,
      SimpleGraph.Walk.length_takeUntil] using hglobalMin q hqW hqLeft
  have hzCandidate := rlc_bookFirstIntersection_mem_orderedCandidateSet
    right hzRight hzLeft hrank hmin
  obtain ⟨m, hm, hleast⟩ := Finset.exists_min_image
    (rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (fun w => (rlc_ambientCrossingWalk gamma.1).support.idxOf w)
    ⟨z, hzCandidate⟩
  exact ⟨m, hm, fun q hq => hleast q hq⟩


theorem rlc_bookMaxOrderedIntersectionCandidate_eq_of_leftLater
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z r : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMax : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
    (hzrLeft :
      (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
        (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX r)) :
    r = z := by
  by_contra hrz
  obtain ⟨q, hqCandidate, hzq, _hqr⟩ :=
    rlc_bookOrderedIntersectionCandidate_exists_later
      hzCandidate hrSet hzrLeft hrz
  exact (not_lt_of_ge (hzMax q hqCandidate)) hzq


theorem rlc_bookMinOrderedIntersectionCandidate_eq_of_rightEarlier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z r : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMin : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q)
    (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
    (hrzRight :
      (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z) :
    r = z := by
  by_contra hrz
  obtain ⟨q, hqCandidate, _hqr, hqz⟩ :=
    rlc_bookOrderedIntersectionCandidate_exists_earlier
      hzCandidate hrSet hrzRight hrz
  exact (not_lt_of_ge (hzMin q hqCandidate)) hqz


theorem rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (z : Site 2)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    ∃ (x y : Site 2)
      (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
      (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)),
      x ∈ (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧
        y ∈ (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        rlc_flipX (rlc_dualReflect x) ∈
          (right.map rlc_flipXLatticeHom).support ∧
        rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
        RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
        RlcBookRightIntersectionRankRealizedAt gamma right ∧
        RlcBookRightPrefixRankAt gamma right := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hzWR : z ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
      hzRight
  have hzWL : rlc_flipX z ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  let right : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) z := WR.takeUntil z hzWR
  let left : (hypercubicLattice 2).Walk
      (rlc_flipX z) (gamma'.1.2.1 : Site 2) :=
    WL.dropUntil (rlc_flipX z) hzWL
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk
      z (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy
      (rlc_flipX_involutive z) hflipUpper
  have hrightEdges : ∀ e ∈ right.edges,
      e ∈ rlc_pathEdges gamma.1 := by
    intro e he
    exact rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
      (WR.edges_takeUntil_subset hzWR he)
  have hleftEdges : ∀ e ∈ left.edges,
      e ∈ rlc_pathEdges gamma'.1 := by
    intro e he
    exact rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
      (WL.edges_dropUntil_subset hzWL he)
  have hflipLeftSupport (v : Site 2) :
      v ∈ flipLeft.support ↔ rlc_flipX v ∈ left.support := by
    dsimp only [flipLeft]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      change rlc_flipX (rlc_flipX w) ∈ left.support
      simpa using hw
    · intro hv
      exact ⟨rlc_flipX v, hv, rlc_flipX_involutive v⟩
  have hflipLeftRank : RlcBookReflectedLeftSuffixRankAt
      gamma' flipLeft := by
    intro v hv
    apply rlc_isPath_idxOf_le_of_mem_dropUntil WL
      (rlc_ambientCrossingWalk_isPath gamma'.1) hzWL
    exact (hflipLeftSupport v).1 hv
  have hrightRank : RlcBookRightIntersectionRankRealizedAt
      gamma right := by
    simp [RlcBookRightIntersectionRankRealizedAt, right, WR,
      SimpleGraph.Walk.length_takeUntil]
  have hrightPrefix : RlcBookRightPrefixRankAt gamma right := by
    intro v hv
    apply rlc_idxOf_le_of_mem_takeUntil WR hzWR
    exact hv
  let flipRight : (hypercubicLattice 2).Walk
      (rlc_flipX (gamma.1.1 : Site 2)) (rlc_flipX z) :=
    right.map rlc_flipXLatticeHom
  have hrightStartFlip : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrightStartH : rlc_flipX (gamma.1.1 : Site 2) ∈ H := by
    rw [hrightStartFlip]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
        (rlc_path_start_mem_vertices gamma.1))
  have hzFlipExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hzLeft
  have hzFlipOut : rlc_flipX z ∉ H := by
    simpa [H, rlc_twoChannelFullFilledReachSet] using hzFlipExt
  have hflipRightTrace : ∀ v ∈ flipRight.support,
      ∃ w ∈ rlc_pathVertices gamma.1, rlc_flipX w = v := by
    intro v hv
    change v ∈ (right.map rlc_flipXLatticeHom).support at hv
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w, ?_, rfl⟩
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hw
    rcases hw with rfl | ⟨e, he, hwe⟩
    · exact hzRight
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := rlc_pathEdge_endpoints_mem_vertices gamma.1
            (hrightEdges s(a, b) he)
          rw [Sym2.mem_iff] at hwe
          exact hwe.elim (fun h => h ▸ hab.1) (fun h => h ▸ hab.2)
  obtain ⟨x, hxSupport, hxPath, hxOrder⟩ :=
    rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit
      gamma.1 H flipRight hflipRightTrace hrightStartH hzFlipOut
  have hzH : z ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet
        gamma gamma' omega hzRight)
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hleftEndExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hleftEndPath
  have hleftEndOut : rlc_flipX (gamma'.1.2.1 : Site 2) ∉ H := by
    rw [hflipUpper]
    simpa [H, rlc_twoChannelFullFilledReachSet] using hleftEndExt
  let flipLeftOrdered : (hypercubicLattice 2).Walk
      (rlc_flipX (rlc_flipX z))
      (rlc_flipX (gamma'.1.2.1 : Site 2)) :=
    flipLeft.copy (rlc_flipX_involutive z).symm hflipUpper.symm
  have hflipLeftTrace : ∀ v ∈ flipLeftOrdered.support,
      ∃ w ∈ rlc_pathVertices gamma'.1, rlc_flipX w = v := by
    intro v hv
    have hv' : v ∈ flipLeft.support := by
      simpa [flipLeftOrdered, SimpleGraph.Walk.support_copy] using hv
    let w := rlc_flipX v
    have hwLeft : w ∈ left.support := (hflipLeftSupport v).1 hv'
    have hwPath : w ∈ rlc_pathVertices gamma'.1 := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hwLeft
      rcases hwLeft with hwend | ⟨e, he, hwe⟩
      · rw [hwend]
        exact hleftEndPath
      · induction e using Sym2.inductionOn with
        | _ a b =>
            have hab := rlc_pathEdge_endpoints_mem_vertices gamma'.1
              (hleftEdges s(a, b) he)
            rw [Sym2.mem_iff] at hwe
            exact hwe.elim (fun h => h ▸ hab.1) (fun h => h ▸ hab.2)
    exact ⟨w, hwPath, by simp [w]⟩
  have hzFlipFlipH : rlc_flipX (rlc_flipX z) ∈ H := by
    simpa using hzH
  obtain ⟨y, hySupport, hyPath, hyOrder⟩ :=
    rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit
      gamma'.1 H flipLeftOrdered hflipLeftTrace hzFlipFlipH hleftEndOut
  have hyOrder' : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support := by
    simpa [flipLeftOrdered, SimpleGraph.Walk.support_copy] using hyOrder
  exact ⟨x, y, right, flipLeft, hxSupport, hySupport, hxPath, hyPath,
    hxOrder, hyOrder', hflipLeftRank, hrightRank, hrightPrefix⟩


theorem rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z y u : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y u)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (huRight : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX r) :
    ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect y = rlc_flipX r ∧
        r ∈ flipLeft.support ∧
        (r = z ∨
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf r) := by
  obtain ⟨r, hrRight, hyr⟩ :=
    rlc_twoChannelFullPhysical_reflectedRightWalk_start q hedges huRight
  have hrSuffix : r ∈ flipLeft.support := by
    rw [hyr] at hyOrder
    simpa using hyOrder
  have hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1 := by
    rw [hyr] at hyLeft
    simpa using hyLeft
  have hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
    simp [rlc_bookFlippedTraceIntersectionSet, hrRight, hrLeft]
  refine ⟨r, hrRight, hyr, hrSuffix, ?_⟩
  by_cases hrz : r = z
  · exact Or.inl hrz
  · exact Or.inr
      (rlc_bookOrderedIntersectionCandidate_rightRank_strict
        hzCandidate hrSet (hflipLeftRank r hrSuffix) hrz)


theorem rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z y u : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y u)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (huRight : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX r) :
    rlc_dualReflect y = rlc_flipX z := by
  obtain ⟨r, hrRight, hyr, hrSuffix, _hprogress⟩ :=
    rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress
      flipLeft q hzCandidate hyLeft hyOrder hflipLeftRank hedges huRight
  have hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1 := by
    rw [hyr] at hyLeft
    simpa using hyLeft
  have hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
    simp [rlc_bookFlippedTraceIntersectionSet, hrRight, hrLeft]
  have hrz := rlc_bookMaxOrderedIntersectionCandidate_eq_of_leftLater
    hzCandidate hzMax hrSet (hflipLeftRank r hrSuffix)
  simpa [hrz] using hyr


theorem rlc_twoChannelFullPhysical_maxCandidate_reflectedRight_contacts
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y u : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y u)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hx : rlc_dualReflect x = z)
    (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (huRight : ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX r) :
    rlc_dualReflect y = rlc_flipX z ∧ x ≠ y := by
  have hy :=
    rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate
      flipLeft q hzCandidate hzMax hyLeft hyOrder hflipLeftRank hedges huRight
  have hzSet := Finset.mem_filter.mp
    (Finset.mem_filter.mp hzCandidate).1
  exact ⟨hy, rlc_twoChannelFullPhysical_intersectionImage_contacts_ne
    hfaith hzSet.1 hzSet.2 hx hy⟩


theorem rlc_twoChannelFullPhysical_rightContact_reflectedLeft_candidateRetreat
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hxRight : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (huLeft : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX l) :
    ∃ r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma',
      rlc_dualReflect x = r ∧
        (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
        (r = z ∨
          ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
                (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧
              (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
                (rlc_ambientCrossingWalk gamma.1).support.idxOf z) := by
  obtain ⟨l, hlLeft, hxl⟩ :=
    rlc_twoChannelFullPhysical_reflectedLeftWalk_start q hedges huLeft
  let r := rlc_dualReflect x
  have hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1 := by
    simpa [r, hxl] using hlLeft
  have hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
    simp [rlc_bookFlippedTraceIntersectionSet, r, hxRight, hrLeft]
  have hrSupport : r ∈ right.support := by
    change rlc_flipX r ∈ (right.map rlc_flipXLatticeHom).support at hxOrder
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxOrder
    obtain ⟨w, hw, hwr⟩ := hxOrder
    have hwr' : w = r := by
      change rlc_flipX w = rlc_flipX r at hwr
      exact rlc_flipX.injective hwr
    simpa [hwr'] using hw
  refine ⟨r, hrSet, rfl, hrightPrefix r hrSupport, ?_⟩
  by_cases hrz : r = z
  · exact Or.inl hrz
  · exact Or.inr
      (rlc_bookOrderedIntersectionCandidate_exists_earlier
        hzCandidate hrSet (hrightPrefix r hrSupport) hrz)


theorem rlc_twoChannelFullPhysical_rightContact_reflectedLeft_eq_of_minCandidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x u)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMin : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q)
    (hxRight : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
    (hedges : ∀ e ∈ q.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (huLeft : ∃ l ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX l) :
    rlc_dualReflect x = z := by
  obtain ⟨r, hrSet, hxr, hrzRight, _hretreat⟩ :=
    rlc_twoChannelFullPhysical_rightContact_reflectedLeft_candidateRetreat
      right q hzCandidate hxRight hxOrder hrightPrefix hedges huLeft
  have hrz := rlc_bookMinOrderedIntersectionCandidate_eq_of_rightEarlier
    hzCandidate hzMin hrSet hrzRight
  simpa [hrz] using hxr


end
end StatMech.Universality
