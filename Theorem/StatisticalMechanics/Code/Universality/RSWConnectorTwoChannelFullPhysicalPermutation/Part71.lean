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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part70
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    (z : Site 2)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
    RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
      gamma gamma' omega z := by
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
  exact ⟨x, y, u, right, flipLeft, c, hx, hy, hcycle,
    hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank, hrightRank,
    hrightPrefix, hbad, hxPlace, hyPlace⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_fixed_or_laterCandidateObstruction
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hxz : rlc_dualReflect x = z) :
    rlc_dualReflect y = rlc_flipX z ∨
      ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          rlc_bookOrderedCandidateReverseRank gamma q <
              rlc_bookOrderedCandidateReverseRank gamma z ∧
            RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
              gamma gamma' omega q := by
  have hzCandidate :=
    rlc_bookFirstIntersection_mem_orderedCandidateSet
      right hzRight hzLeft hrank hmin
  obtain ⟨_hqrLeft, _hxz, _hqlRight, r, hrRight, hyr, hrSupport,
      hrz | hzlt⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateProgress
      hfaith flipLeft qr ql hzCandidate hyPath hyOrder hflipLeftRank
        hrow.1 hxz hrow.2.2.1 (Or.inr hrow.2.2.2)
  · exact Or.inl (by simpa [hrz] using hyr)
  · have hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1 := by
      rw [← hyr]
      exact hyPath
    have hrSet : r ∈
        rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
      simp [rlc_bookFlippedTraceIntersectionSet, hrRight, hrLeft]
    have hrne : r ≠ z := by
      intro hrz
      subst r
      simp at hzlt
    obtain ⟨q, hqCandidate, hzq, _hqr⟩ :=
      rlc_bookOrderedIntersectionCandidate_exists_later
        hzCandidate hrSet (hflipLeftRank r hrSupport) hrne
    exact Or.inr ⟨q, hqCandidate, hzq,
      rlc_bookOrderedCandidateReverseRank_lt_of_rightRank_lt
        hzCandidate hqCandidate hzq,
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood
        gamma gamma' hfaith omega hno hnoGood q hqCandidate⟩


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowTwo_fixed_or_lowerRank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hxz : rlc_dualReflect x = z) :
    rlc_dualReflect y = rlc_flipX z ∨
      ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          rlc_bookOrderedCandidateReverseRank gamma q <
              rlc_bookOrderedCandidateReverseRank gamma z ∧
            RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) q := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega :=
    rlc_twoChannelFullPhysical_noGoodComponent_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
  exact
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_fixed_or_laterCandidateObstruction
      hfaith hno hnoGood right flipLeft hzRight hzLeft hyPath hyOrder
        hflipLeftRank hrank hmin qr ql hrow hxz


theorem
    rlc_twoChannelFullPhysical_noPair_exactRows_fixedRowTwo_or_lowerRank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrows : RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
          flipLeft qr ql) :
    RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql ∨
      (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql ∧
        rlc_dualReflect x = z ∧
        rlc_dualReflect y = rlc_flipX z) ∨
      (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          rlc_bookOrderedCandidateReverseRank gamma q <
              rlc_bookOrderedCandidateReverseRank gamma z ∧
            RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
              gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) q) ∨
      RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql ∨
      RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
            qr ql := by
  rcases hrows with hrow1 | hrow2 | hrow3 | hrow4
  · exact Or.inl hrow1.1
  · rcases hrow2 with ⟨hrow, hxz, _r, _hr, _hyr, _hrSupport⟩
    rcases
        rlc_twoChannelFullPhysical_noPair_wallFamilyRowTwo_fixed_or_lowerRank
          hfaith A B hAright hAleft hBright hBleft hnoPair right flipLeft
            hzRight hzLeft hyPath hyOrder hflipLeftRank hrank hmin qr ql
              hrow hxz with hfixed | hlower
    · exact Or.inr (Or.inl ⟨hrow, hxz, hfixed⟩)
    · exact Or.inr (Or.inr (Or.inl hlower))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrow3.1)))
  · obtain ⟨_r, hrow, _hxAxis, _hr, _hyr, _hrSupport, _hrank⟩ := hrow4
    exact Or.inr (Or.inr (Or.inr (Or.inr hrow)))


theorem
    rlc_twoChannelFullPhysical_noPair_exactRows_lowerRank_of_rowEliminators
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
    (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrowOne : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
        gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
            qr ql →
        rlc_dualReflect x = z →
        rlc_dualReflect y = (gamma'.1.2.1 : Site 2) →
        (let W := (rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom;
          W.support.idxOf (rlc_dualReflect ur) <
            W.support.idxOf (rlc_dualReflect ul)) → False)
    (hrowTwo : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
          gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              qr ql →
        rlc_dualReflect x = z →
        rlc_dualReflect y = rlc_flipX z → False)
    (hrowThree : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
        gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
            qr ql →
        rlc_dualReflect x = (gamma.1.1 : Site 2) →
        rlc_dualReflect y = (gamma'.1.2.1 : Site 2) →
        (∃ (hzR : rlc_flipX z ∈
              (((rlc_ambientCrossingWalk gamma.1).map
                rlc_flipXLatticeHom).reverse).support)
            (hzL : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).support),
          rlc_dualReflect ur ∈
              ((((rlc_ambientCrossingWalk gamma.1).map
                rlc_flipXLatticeHom).reverse).dropUntil
                  (rlc_flipX z) hzR).support ∧
            rlc_dualReflect ul ∈
              (((rlc_ambientCrossingWalk gamma'.1).map
                rlc_flipXLatticeHom).dropUntil z hzL).support) → False)
    (hrowFour : ∀ r : Site 2,
        RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
                qr ql →
          rlc_dualReflect x = (gamma.1.1 : Site 2) →
          r ∈ rlc_pathVertices gamma.1 →
          rlc_dualReflect y = rlc_flipX r →
          r ∈ flipLeft.support →
          (let W := ((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse;
            W.support.idxOf (rlc_dualReflect ul) <
              W.support.idxOf (rlc_dualReflect ur)) → False)
    (hrows : RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
          flipLeft qr ql) :
    ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
        rlc_bookOrderedCandidateReverseRank gamma q <
            rlc_bookOrderedCandidateReverseRank gamma z ∧
          RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) q := by
  rcases hrows with hrow1 | hrow2 | hrow3 | hrow4
  · exact False.elim
      (hrowOne hrow1.1 hrow1.2.1 hrow1.2.2.1 hrow1.2.2.2)
  · rcases hrow2 with ⟨hrow, hxz, _r, _hr, _hyr, _hrSupport⟩
    rcases
        rlc_twoChannelFullPhysical_noPair_wallFamilyRowTwo_fixed_or_lowerRank
          hfaith A B hAright hAleft hBright hBleft hnoPair right flipLeft
            hzRight hzLeft hyPath hyOrder hflipLeftRank hrank hmin qr ql
              hrow hxz with hfixed | hlower
    · exact False.elim (hrowTwo hrow hxz hfixed)
    · exact hlower
  · exact False.elim
      (hrowThree hrow3.1 hrow3.2.1 hrow3.2.2.1 hrow3.2.2.2)
  · obtain ⟨r, hrow, hxAxis, hr, hyr, hrSupport, horder⟩ := hrow4
    exact False.elim
      (hrowFour r hrow hxAxis hr hyr hrSupport horder)


theorem
    rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haSupport : a ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (haCycle : a ∈ c.support)
    (z : Site 2)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
    RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
      gamma gamma' omega c z := by
  have hzIntersection := (Finset.mem_filter.mp hzCandidate).1
  have hzMem := Finset.mem_filter.mp hzIntersection
  obtain ⟨x, y, right, flipLeft, hxSupport, hySupport, hxPath, hyPath,
      hxOrder, hyOrder, hflipLeftRank, hrightRank, hrightPrefix⟩ :=
    rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
      gamma gamma' hfaith omega hno z hzMem.1 hzMem.2
  have hx : x ∈ c.support :=
    rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport
      gamma gamma' omega c hcycle haSupport haCycle hxSupport
  have hy : y ∈ c.support :=
    rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport
      gamma gamma' omega c hcycle haSupport haCycle hySupport
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
  exact ⟨x, y, right, flipLeft, hx, hy, hcycle,
    hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank, hrightRank,
    hrightPrefix, hbad, hxPlace, hyPlace⟩


theorem
    rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle ∧
        rlc_twoChannelFullFilledReachSet gamma gamma' omega =
          jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
            gamma gamma' omega c z := by
  obtain ⟨z, hzCandidate, _hzMin⟩ :=
    rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith
  have hzIntersection := (Finset.mem_filter.mp hzCandidate).1
  have hzMem := Finset.mem_filter.mp hzIntersection
  obtain ⟨x, y, _right, _flipLeft, hxSupport, hySupport, _hxPath, _hyPath,
      _hxOrder, _hyOrder, _hflipLeftRank, _hrightRank, _hrightPrefix⟩ :=
    rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
      gamma gamma' hfaith omega hno z hzMem.1 hzMem.2
  obtain ⟨u, c, hcycle, hx, _hy⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts
      gamma gamma' omega hxSupport hySupport
  refine ⟨u, c, hcycle,
    rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle, ?_⟩
  intro q hqCandidate
  exact
    rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood
      gamma gamma' hfaith omega hno hnoGood c hcycle hxSupport hx
        q hqCandidate


theorem
    rlc_twoChannelFullPhysical_staticCutFailure_globalOrderedObstruction
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hfailure : ¬∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧
        rlc_connectorOnLeft gamma' y ∧
          (rlc_twoChannelFullPhysicalCutTargetGraphAt
            gamma gamma' A).Reachable x y) :
    let omega :=
      rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle ∧
        rlc_twoChannelFullFilledReachSet gamma gamma' omega =
          jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        rlc_twoChannelFullReachSet gamma gamma' omega ⊆
          rlc_twoChannelFullPhysicalLiftVertexCut A ∧
          ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
            RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
              gamma gamma' omega c z := by
  dsimp only
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega := by
    intro hgood
    exact hfailure
      (rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent
        gamma gamma' A hAright hAleft hgood)
  obtain ⟨u, c, hcycle, horient, hall⟩ :=
    rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle
      gamma gamma' hfaith omega hno hnoGood
  exact ⟨u, c, hcycle, horient,
    rlc_twoChannelFullReachSet_subset_staticCut
      gamma gamma' A hAright hAleft, hall⟩


theorem rlc_twoChannelFullPhysical_fixedExtremalContactsOnCycle_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haSupport : a ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (haCycle : a ∈ c.support) :
    ∃ x y : Site 2,
      x ∈ c.support ∧ y ∈ c.support ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          ∃ (right : (hypercubicLattice 2).Walk
              (gamma.1.1 : Site 2) z)
            (flipLeft : (hypercubicLattice 2).Walk
              z (gamma'.1.2.1 : Site 2)),
            rlc_flipX (rlc_dualReflect x) ∈
                (right.map rlc_flipXLatticeHom).support ∧
              rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
              RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
              RlcBookRightIntersectionRankRealizedAt gamma right ∧
              RlcBookRightPrefixRankAt gamma right := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  obtain ⟨zMin, hzMinCandidate, hzMin⟩ :=
    rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith
  obtain ⟨zMax, hzMaxCandidate, hzMax⟩ :=
    rlc_exists_max_bookOrderedIntersectionCandidate gamma gamma' hfaith
  have hzMinSet := Finset.mem_filter.mp
    (Finset.mem_filter.mp hzMinCandidate).1
  have hzMaxSet := Finset.mem_filter.mp
    (Finset.mem_filter.mp hzMaxCandidate).1
  obtain ⟨x, _yMin, rightMin, _flipLeftMin, hxSupport, _hyMinSupport,
      hxPath, _hyMinPath, hxOrderMin, _hyOrderMin, _hleftMin,
      _hrankMin, hprefixMin⟩ :=
    rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
      gamma gamma' hfaith omega hno zMin hzMinSet.1 hzMinSet.2
  obtain ⟨_xMax, y, _rightMax, flipLeftMax, _hxMaxSupport, hySupport,
      _hxMaxPath, hyPath, _hxOrderMax, hyOrderMax, hleftMax,
      _hrankMax, _hprefixMax⟩ :=
    rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure
      gamma gamma' hfaith omega hno zMax hzMaxSet.1 hzMaxSet.2
  have hxCycle : x ∈ c.support :=
    rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport
      gamma gamma' omega c hcycle haSupport haCycle hxSupport
  have hyCycle : y ∈ c.support :=
    rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport
      gamma gamma' omega c hcycle haSupport haCycle hySupport
  have hxRightMin : rlc_dualReflect x ∈ rightMin.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxOrderMin
    obtain ⟨w, hw, hwx⟩ := hxOrderMin
    have hwEq : w = rlc_dualReflect x := by
      apply rlc_flipX.injective
      exact hwx
    simpa [hwEq] using hw
  have hxRankMin : WR.support.idxOf (rlc_dualReflect x) ≤
      WR.support.idxOf zMin := by
    simpa [WR] using hprefixMin _ hxRightMin
  have hyRankMax : WL.support.idxOf (rlc_flipX zMax) ≤
      WL.support.idxOf (rlc_dualReflect y) := by
    have := hleftMax _ hyOrderMax
    simpa [WL] using this
  refine ⟨x, y, hxCycle, hyCycle, hxPath, hyPath, ?_⟩
  intro z hzCandidate
  have hzSet := Finset.mem_filter.mp
    (Finset.mem_filter.mp hzCandidate).1
  have hzWR : z ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
      hzSet.1
  have hzWL : rlc_flipX z ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzSet.2
  let right : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) z := WR.takeUntil z hzWR
  let left : (hypercubicLattice 2).Walk
      (rlc_flipX z) (gamma'.1.2.1 : Site 2) :=
    WL.dropUntil (rlc_flipX z) hzWL
  have hleftEndFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk
      z (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy
      (rlc_flipX_involutive z) hleftEndFlip
  have hxWR : rlc_dualReflect x ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma.1 (rlc_dualReflect x)).2 hxPath
  have hxRight : rlc_dualReflect x ∈ right.support := by
    apply (rlc_mem_takeUntil_iff_idxOf_le WR hzWR hxWR).2
    exact hxRankMin.trans (hzMin z hzCandidate)
  have hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_dualReflect x, hxRight, rfl⟩
  have hzLeftLeMax : WL.support.idxOf (rlc_flipX z) ≤
      WL.support.idxOf (rlc_flipX zMax) := by
    by_cases hzEq : z = zMax
    · simp [hzEq]
    · have hzRightLt : WR.support.idxOf z < WR.support.idxOf zMax := by
        have hle := hzMax z hzCandidate
        have hne : WR.support.idxOf z ≠ WR.support.idxOf zMax := by
          intro heq
          apply hzEq
          exact (List.idxOf_inj hzWR).1 (by simpa [WR] using heq)
        simpa [WR] using lt_of_le_of_ne hle hne
      exact le_of_lt
        ((rlc_bookOrderedIntersectionCandidates_order_agree
          hzMaxCandidate hzCandidate).mp (by simpa [WR] using hzRightLt))
  have hyWL : rlc_dualReflect y ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_dualReflect y)).2 hyPath
  have hyLeft : rlc_dualReflect y ∈ left.support := by
    apply (rlc_isPath_mem_dropUntil_iff_idxOf_le WL
      (rlc_ambientCrossingWalk_isPath gamma'.1) hzWL hyWL).2
    exact hzLeftLeMax.trans hyRankMax
  have hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support := by
    dsimp only [flipLeft]
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_dualReflect y, hyLeft, rfl⟩
  have hflipLeftRank : RlcBookReflectedLeftSuffixRankAt
      gamma' flipLeft := by
    intro v hv
    dsimp only [flipLeft] at hv
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_map, List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have hwWL := WL.support_dropUntil_subset hzWL hw
    simpa [WL, rlc_flipXLatticeHom, rlc_flipX, rlc_flipXFun] using
      (rlc_isPath_idxOf_le_of_mem_dropUntil WL
        (rlc_ambientCrossingWalk_isPath gamma'.1) hzWL hw)
  have hrightRank : RlcBookRightIntersectionRankRealizedAt
      gamma right := by
    simp [RlcBookRightIntersectionRankRealizedAt, right, WR,
      SimpleGraph.Walk.length_takeUntil]
  have hrightPrefix : RlcBookRightPrefixRankAt gamma right := by
    intro v hv
    simpa [WR] using rlc_idxOf_le_of_mem_takeUntil WR hzWR hv
  exact ⟨right, flipLeft, hxOrder, hyOrder, hflipLeftRank,
    hrightRank, hrightPrefix⟩


theorem rlc_twoChannelFullPhysical_fixedContactNoGoodObstructionOnCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haSupport : a ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (haCycle : a ∈ c.support) :
    ∃ (x y : Site 2) (hx : x ∈ c.support) (hy : y ∈ c.support),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
          gamma gamma' omega c hx hy ∧
        ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
        ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) ∧
        ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          ∃ (right : (hypercubicLattice 2).Walk
              (gamma.1.1 : Site 2) z)
            (flipLeft : (hypercubicLattice 2).Walk
              z (gamma'.1.2.1 : Site 2)),
            rlc_flipX (rlc_dualReflect x) ∈
                (right.map rlc_flipXLatticeHom).support ∧
              rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
              RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
              RlcBookRightIntersectionRankRealizedAt gamma right ∧
              RlcBookRightPrefixRankAt gamma right := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath, hall⟩ :=
    rlc_twoChannelFullPhysical_fixedExtremalContactsOnCycle_of_failure
      gamma gamma' hfaith omega hno c hcycle haSupport haCycle
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
  exact ⟨x, y, hx, hy, hxPath, hyPath, hbad,
    hxPlace, hyPlace, hall⟩


theorem
    rlc_twoChannelFullPhysical_staticCutFailure_extremalObstructionsOnCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hfailure : ¬∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧
        rlc_connectorOnLeft gamma' y ∧
          (rlc_twoChannelFullPhysicalCutTargetGraphAt
            gamma gamma' A).Reachable x y) :
    let omega :=
      rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
      (zMin zMax : Site 2),
      c.IsCycle ∧
        rlc_twoChannelFullFilledReachSet gamma gamma' omega =
          jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        rlc_twoChannelFullReachSet gamma gamma' omega ⊆
          rlc_twoChannelFullPhysicalLiftVertexCut A ∧
        zMin ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        zMax ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax) ∧
        RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
          gamma gamma' omega c zMin ∧
        RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
          gamma gamma' omega c zMax := by
  dsimp only
  obtain ⟨u, c, hcycle, horient, hreachA, hall⟩ :=
    rlc_twoChannelFullPhysical_staticCutFailure_globalOrderedObstruction
      gamma gamma' hfaith A hAright hAleft hfailure
  obtain ⟨zMin, hzMinCandidate, hzMin⟩ :=
    rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith
  obtain ⟨zMax, hzMaxCandidate, hzMax⟩ :=
    rlc_exists_max_bookOrderedIntersectionCandidate gamma gamma' hfaith
  exact ⟨u, c, zMin, zMax, hcycle, horient, hreachA,
    hzMinCandidate, hzMaxCandidate, hzMin, hzMax,
    hall zMin hzMinCandidate, hall zMax hzMaxCandidate⟩


theorem
    rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructionsOnCycle_of_noGood
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
      (zMin zMax : Site 2),
      c.IsCycle ∧
        rlc_twoChannelFullFilledReachSet gamma gamma' omega =
          jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        zMin ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        zMax ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax) ∧
        RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
          gamma gamma' omega c zMin ∧
        RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
          gamma gamma' omega c zMax := by
  obtain ⟨u, c, hcycle, horient, hall⟩ :=
    rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle
      gamma gamma' hfaith omega hno hnoGood
  obtain ⟨zMin, hzMinCandidate, hzMin⟩ :=
    rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith
  obtain ⟨zMax, hzMaxCandidate, hzMax⟩ :=
    rlc_exists_max_bookOrderedIntersectionCandidate gamma gamma' hfaith
  exact ⟨u, c, zMin, zMax, hcycle, horient, hzMinCandidate,
    hzMaxCandidate, hzMin, hzMax, hall zMin hzMinCandidate,
    hall zMax hzMaxCandidate⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselect
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    (rlc_dualReflect x = z ∧
        rlc_dualReflect y = rlc_flipX z) ∨
      (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
          RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
            gamma gamma' omega q) ∨
      ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
            gamma gamma' omega q := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition
        hzCandidate hyPath hflipLeftRank hbracket with
    hfixed | ⟨q, hqCandidate, hqz⟩ | ⟨q, hqCandidate, hzq⟩
  · exact Or.inl hfixed
  · exact Or.inr (Or.inl ⟨q, hqCandidate, hqz,
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood
        gamma gamma' hfaith omega hno hnoGood q hqCandidate⟩)
  · exact Or.inr (Or.inr ⟨q, hqCandidate, hzq,
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood
        gamma gamma' hfaith omega hno hnoGood q hqCandidate⟩)


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselectOnCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u a : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haSupport : a ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (haCycle : a ∈ c.support)
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    (rlc_dualReflect x = z ∧
        rlc_dualReflect y = rlc_flipX z) ∨
      (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
          RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
            gamma gamma' omega c q) ∨
      ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧
          RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
            gamma gamma' omega c q := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition
        hzCandidate hyPath hflipLeftRank hbracket with
    hfixed | ⟨q, hqCandidate, hqz⟩ | ⟨q, hqCandidate, hzq⟩
  · exact Or.inl hfixed
  · exact Or.inr (Or.inl ⟨q, hqCandidate, hqz,
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood
        gamma gamma' hfaith omega hno hnoGood c hcycle haSupport haCycle
          q hqCandidate⟩)
  · exact Or.inr (Or.inr ⟨q, hqCandidate, hzq,
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood
        gamma gamma' hfaith omega hno hnoGood c hcycle haSupport haCycle
          q hqCandidate⟩)


theorem
    rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructions_of_noGood
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    ∃ zMin zMax : Site 2,
      zMin ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        zMax ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧
        (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma',
          (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
            (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax) ∧
        (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤
          (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax ∧
        RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
          gamma gamma' omega zMin ∧
        RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt
          gamma gamma' omega zMax := by
  obtain ⟨zMin, hzMinCandidate, hzMin⟩ :=
    rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith
  obtain ⟨zMax, hzMaxCandidate, hzMax⟩ :=
    rlc_exists_max_bookOrderedIntersectionCandidate gamma gamma' hfaith
  refine ⟨zMin, zMax, hzMinCandidate, hzMaxCandidate, hzMin, hzMax,
    hzMin zMax hzMaxCandidate, ?_, ?_⟩
  · exact
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood
        gamma gamma' hfaith omega hno hnoGood zMin hzMinCandidate
  · exact
      rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood
        gamma gamma' hfaith omega hno hnoGood zMax hzMaxCandidate


end
end StatMech.Universality
