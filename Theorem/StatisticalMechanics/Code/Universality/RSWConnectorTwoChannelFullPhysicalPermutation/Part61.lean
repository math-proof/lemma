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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part61
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket_cases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases
      gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
  rcases h with ⟨hr, hs⟩
  obtain ⟨r, hrSet, hxr, hrle, hrCase⟩ := hr
  obtain ⟨s, hsPath, hys, hsSupport, hsCase⟩ := hs
  rcases hrCase with hrz | hrearlier
  · rcases hsCase with hsz | hslater
    · exact Or.inl
        ⟨by simpa [hrz] using hxr, by simpa [hsz] using hys⟩
    · exact Or.inr (Or.inr (Or.inl
        ⟨by simpa [hrz] using hxr,
          ⟨s, hsPath, hys, hsSupport, hslater⟩⟩))
  · rcases hsCase with hsz | hslater
    · exact Or.inr (Or.inl
        ⟨⟨r, hrSet, hxr, hrle, hrearlier⟩,
          by simpa [hsz] using hys⟩)
    · exact Or.inr (Or.inr (Or.inr
        ⟨⟨r, hrSet, hxr, hrle, hrearlier⟩,
          ⟨s, hsPath, hys, hsSupport, hslater⟩⟩))


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    (rlc_dualReflect x = z ∧
        rlc_dualReflect y = rlc_flipX z) ∨
      (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z) ∨
      ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
  rcases h with ⟨hr, hs⟩
  obtain ⟨r, hrSet, hxr, _hrle, hrCase⟩ := hr
  obtain ⟨s, hsPath, hys, hsSupport, hsCase⟩ := hs
  by_cases hrz : r = z
  · by_cases hsz : s = z
    · exact Or.inl ⟨hxr.trans hrz, hys.trans (congrArg rlc_flipX hsz)⟩
    · right
      right
      have hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1 := by
        rw [hys] at hyPath
        simpa using hyPath
      have hsSet : s ∈
          rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
        simp [rlc_bookFlippedTraceIntersectionSet, hsPath, hsLeft]
      obtain ⟨q, hqCandidate, hzq, _hqs⟩ :=
        rlc_bookOrderedIntersectionCandidate_exists_later
          hzCandidate hsSet (hflipLeftRank s hsSupport) hsz
      exact ⟨q, hqCandidate, hzq⟩
  · obtain ⟨q, hqCandidate, _hqr, hqz⟩ := Or.resolve_left hrCase hrz
    exact Or.inr (Or.inl ⟨q, hqCandidate, hqz⟩)


theorem rlc_rightAmbientTrace_segment_of_idxOf_le
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {a b : Site 2}
    (haPath : a ∈ rlc_pathVertices gamma.1)
    (hbPath : b ∈ rlc_pathVertices gamma.1)
    (hab : (rlc_ambientCrossingWalk gamma.1).support.idxOf a ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf b) :
    ∃ P : (hypercubicLattice 2).Walk a b,
      ∀ v ∈ P.support, v ∈ (rlc_ambientCrossingWalk gamma.1).support := by
  let W := rlc_ambientCrossingWalk gamma.1
  have haW : a ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 a).2
      haPath
  have hbW : b ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 b).2
      hbPath
  have hbSuffix : b ∈ (W.dropUntil a haW).support :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le W
      (rlc_ambientCrossingWalk_isPath gamma.1) haW hbW).2 hab
  let P := (W.dropUntil a haW).takeUntil b hbSuffix
  refine ⟨P, ?_⟩
  intro v hv
  exact W.support_dropUntil_subset haW
    ((W.dropUntil a haW).support_takeUntil_subset_support hbSuffix hv)


theorem rlc_rightAmbientTrace_prefix_meets_segment_only_start
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {a b v : Site 2}
    (haPath : a ∈ rlc_pathVertices gamma.1)
    (hbPath : b ∈ rlc_pathVertices gamma.1)
    (hab : (rlc_ambientCrossingWalk gamma.1).support.idxOf a ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf b)
    (hvPrefix : v ∈ ((rlc_ambientCrossingWalk gamma.1).takeUntil a
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 a).2 haPath)).support)
    (hvSegment : v ∈ (((rlc_ambientCrossingWalk gamma.1).dropUntil a
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 a).2 haPath)).takeUntil b
          ((rlc_isPath_mem_dropUntil_iff_idxOf_le
            (rlc_ambientCrossingWalk gamma.1)
            (rlc_ambientCrossingWalk_isPath gamma.1)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma.1 a).2 haPath)
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
              gamma.1 b).2 hbPath)).2 hab)).support) :
    v = a := by
  let W := rlc_ambientCrossingWalk gamma.1
  have haW : a ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 a).2
      haPath
  have hbW : b ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 b).2
      hbPath
  have hbSuffix : b ∈ (W.dropUntil a haW).support :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le W
      (rlc_ambientCrossingWalk_isPath gamma.1) haW hbW).2 hab
  have hvSuffix : v ∈ (W.dropUntil a haW).support :=
    (W.dropUntil a haW).support_takeUntil_subset_support hbSuffix hvSegment
  have hvW : v ∈ W.support := W.support_dropUntil_subset haW hvSuffix
  have hva : W.support.idxOf v ≤ W.support.idxOf a :=
    rlc_idxOf_le_of_mem_takeUntil W haW hvPrefix
  have hav : W.support.idxOf a ≤ W.support.idxOf v :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le W
      (rlc_ambientCrossingWalk_isPath gamma.1) haW hvW).1 hvSuffix
  exact (List.idxOf_inj hvW).1 (by omega)


theorem RlcBookFaithfulTracePair.dualSymm_images_ne
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {r l : Site 2}
    (hr : r ∈ rlc_pathVertices gamma.1)
    (hl : l ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflect.symm r ≠ rlc_dualReflect.symm l := by
  intro h
  have hrl : r = l := rlc_dualReflect.symm.injective h
  exact (Finset.disjoint_left.mp hfaith.exposed_disjoint) hr
    (hrl ▸ hl)


end
end StatMech.Universality
