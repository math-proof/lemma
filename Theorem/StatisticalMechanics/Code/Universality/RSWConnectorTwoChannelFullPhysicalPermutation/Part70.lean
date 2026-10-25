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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part69
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_of_product
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hproduct : RlcTwoChannelFullPhysicalWallTerminalProductClassification
      gamma gamma' omega (vr := vr) (vl := vl) qr ql) :
    RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
      gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
  rcases hproduct.rightPrefix with hallR | hbadR
  · rcases hproduct.leftPrefix with hallL | hbadL
    · rcases hproduct.rightTerminal with hlocR | hlocalizedR
      · rcases hproduct.leftTerminal with hlocL | hlocalizedL
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (hproduct.terminalTable hallR hallL hlocR hlocL))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hlocalizedL.2)))
      · exact Or.inr (Or.inr (Or.inl hlocalizedR.2))
    · exact Or.inr (Or.inl hbadL)
  · exact Or.inl hbadR


theorem rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad
      gamma gamma' omega ur vr)
    (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad
      gamma gamma' omega ul vl)
    (hcases : RlcTwoChannelFullPhysicalTetheredWallTerminalFamilyAlternative
      gamma gamma' omega qr ql) :
    RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
      gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
  rcases hcases with hR | hL | hUr | hUl | htable
  · exact Or.inl
      ((rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge qr).mp hR)
  · exact Or.inr (Or.inl
      ((rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge ql).mp hL))
  · exact Or.inr (Or.inr (Or.inl
      (rlc_rightArcClassifiedBad_of_terminal_not_exclusive hclassR hUr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (rlc_leftArcClassifiedBad_of_terminal_not_exclusive hclassL hUl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htable)))


theorem rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_withDirections
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
      (W : (hypercubicLattice 2).Walk ur ul)
      (hurv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
      (hulv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
      rlc_orderedContourArc c hx hy =
          (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons hurv rr) ∧
        (rlc_complementaryContourArc c hx hy).reverse =
          (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons hulv rl) ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ur vr ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ul vl ∧
        RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega ur vr ∧
        RlcTwoChannelFullPhysicalLeftArcClassifiedBad
          gamma gamma' omega ul vl ∧
        (∀ v ∈ W.support,
          v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
        RlcTwoChannelFullPhysicalTetheredWallTerminalFamilyAlternative
          gamma gamma' omega qr ql := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, W, hurv, hulv,
      hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL, hWBox⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk_withDirections hbad
  refine ⟨ur, vr, ul, vl, qr, rr, ql, rl, W, hurv, hulv,
    hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL, hWBox, ?_⟩
  by_cases hallR : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
  · by_cases hallL : ∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hurLoc :
          RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
              gamma gamma' (rlc_dualReflect ur) ∨
            RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' (rlc_dualReflect ur)
      · by_cases hulLoc :
            RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
                gamma gamma' (rlc_dualReflect ul) ∨
              RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' (rlc_dualReflect ul)
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (rlc_twoChannelFullPhysical_twoArcWallTerminalFamilyTable
              hfaith qr ql hxPath hyPath hallR hallL hurLoc hulLoc))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hulLoc)))
      · exact Or.inr (Or.inr (Or.inl hurLoc))
    · exact Or.inr (Or.inl hallL)
  · exact Or.inl hallR


theorem rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_atMaxCandidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMax : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
      (W : (hypercubicLattice 2).Walk ur ul)
      (hurv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
      (hulv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
      rlc_orderedContourArc c hx hy =
          (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons hurv rr) ∧
        (rlc_complementaryContourArc c hx hy).reverse =
          (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons hulv rl) ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ur vr ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ul vl ∧
        RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega ur vr ∧
        RlcTwoChannelFullPhysicalLeftArcClassifiedBad
          gamma gamma' omega ul vl ∧
        (∀ v ∈ W.support,
          v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
        RlcTwoChannelFullPhysicalTetheredWallTerminalFamilyAlternative
          gamma gamma' omega qr ql ∧
        RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative
          gamma gamma' omega (vr := vr) (vl := vl) qr ql ∧
        (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
            gamma gamma' omega qr ql →
          rlc_dualReflect y = rlc_flipX z ∧
            RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
                gamma gamma' (z := z) (x := x) (y := y) flipLeft ∧
              RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases
                  gamma gamma' (z := z) (x := x) (y := y) flipLeft ∧
                RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases
                  gamma gamma' (z := z) (x := x) (y := y) flipLeft) := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, W, hurv, hulv,
      hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL, hWBox, hcases⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_withDirections
      hfaith hxPath hyPath hbad
  have hlocalized :=
    rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative
      hclassR hclassL hcases
  refine ⟨ur, vr, ul, vl, qr, rr, ql, rl, W, hurv, hulv,
    hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL, hWBox, hcases,
    hlocalized, ?_⟩
  intro hrow
  have hbracket :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket
      hfaith right flipLeft qr ql hzCandidate hxPath hyPath hxOrder hyOrder
        hrightPrefix hflipLeftRank hrow.1 hrow.2.2.1
          (Or.inl hrow.2.1) (Or.inr hrow.2.2.2)
  have hyEq :=
    rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate
      flipLeft ql hzCandidate hzMax hyPath hyOrder hflipLeftRank
        hrow.2.2.1 hrow.2.2.2.2.1
  have horder :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket_cases
      hbracket
  exact ⟨hyEq, hbracket, horder,
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceSegmentCases
      hzCandidate horder⟩


theorem rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hclassified : RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
      hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL⟩ := hclassified
  have hright : RlcTwoChannelFullPhysicalRightArcClassifiedBad
      gamma gamma' omega ur vr := by
    rcases hclassR with ⟨htarget, hplace⟩ |
        ⟨p, q, hpq, hpqAdj, hpReach, hqFilled, hpPlace⟩
    · left
      refine ⟨htarget, ?_⟩
      rcases hplace with hbarrier | hboundary
      · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
            gamma gamma' hbarrier with
          hright | hleft | hflipLeft | hflipRight
        · exact Or.inl hright
        · exact False.elim
            ((rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact
              hnoGood hxPath qr) hleft)
        · exact Or.inr (Or.inl hflipLeft)
        · exact Or.inr (Or.inr (Or.inl hflipRight))
      · exact Or.inr (Or.inr (Or.inr hboundary))
    · right
      refine ⟨p, q, hpq, hpqAdj, hpReach, hqFilled, ?_⟩
      rcases hpPlace with hpBarrier | hpBoundary
      · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
            gamma gamma' hpBarrier with
          hpRight | hpLeft | hpFlipLeft | hpFlipRight
        · exact Or.inl hpRight
        · exact False.elim
            ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
              gamma gamma' omega hno hpLeft) hpReach)
        · exact Or.inr (Or.inl hpFlipLeft)
        · exact Or.inr (Or.inr (Or.inl hpFlipRight))
      · exact Or.inr (Or.inr (Or.inr hpBoundary))
  have hleft : RlcTwoChannelFullPhysicalLeftArcClassifiedBad
      gamma gamma' omega ul vl := by
    rcases hclassL with ⟨htarget, hplace⟩ |
        ⟨p, q, hpq, hpqAdj, hpReach, hqFilled, hpPlace⟩
    · left
      refine ⟨htarget, ?_⟩
      rcases hplace with hbarrier | hboundary
      · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
            gamma gamma' hbarrier with
          hright | hleft | hflipLeft | hflipRight
        · exact False.elim
            ((rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact
              hnoGood hyPath ql) hright)
        · exact Or.inl hleft
        · exact Or.inr (Or.inl hflipLeft)
        · exact Or.inr (Or.inr (Or.inl hflipRight))
      · exact Or.inr (Or.inr (Or.inr hboundary))
    · right
      refine ⟨p, q, hpq, hpqAdj, hpReach, hqFilled, ?_⟩
      rcases hpPlace with hpBarrier | hpBoundary
      · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
            gamma gamma' hpBarrier with
          hpRight | hpLeft | hpFlipLeft | hpFlipRight
        · exact Or.inl hpRight
        · exact False.elim
            ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
              gamma gamma' omega hno hpLeft) hpReach)
        · exact Or.inr (Or.inl hpFlipLeft)
        · exact Or.inr (Or.inr (Or.inl hpFlipRight))
      · exact Or.inr (Or.inr (Or.inr hpBoundary))
  exact ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
    hdecR, hdecL, hne, hbadR, hbadL, hright, hleft⟩


theorem rlc_twoChannelFullPhysical_firstIntersection_twoArcClassified_of_noGood
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
        z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        rlc_flipX (rlc_dualReflect x) ∈
          (right.map rlc_flipXLatticeHom).support ∧
        rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
        RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
        (∀ w ∈ right.support,
          rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧
        RlcBookRightIntersectionRankRealizedAt gamma right ∧
        RlcBookRightIntersectionRankMinimalAt gamma gamma' right ∧
        RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt
          gamma gamma' omega c hx hy ∧
        ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
        ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
  obtain ⟨z, x, y, u, right, flipLeft, c, hcycle, hx, hy,
      hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank,
      hfirst,
      hrankRealized, hglobalMin⟩ :=
    rlc_twoChannelFullPhysical_firstIntersectionContactCycle_of_failure
      gamma gamma' hfaith omega hno
  have hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy := by
    intro hside
    exact hnoGood
      (rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide
        gamma gamma' omega c hx hy hxPath hyPath hside)
  obtain ⟨hclassified, hxPlace, hyPlace⟩ :=
    rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad
      hfaith omega c hcycle.isTrail hx hy hxPath hyPath hbadSide
  exact ⟨z, x, y, u, right, flipLeft, c, hx, hy,
    hcycle, hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder,
    hflipLeftRank, hfirst,
    hrankRealized, hglobalMin,
    hclassified, hxPlace, hyPlace⟩


theorem rlc_twoChannelFullPhysical_firstIntersection_twoArcNoGood_of_noGood
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
        z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        rlc_flipX (rlc_dualReflect x) ∈
          (right.map rlc_flipXLatticeHom).support ∧
        rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
        RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
        (∀ w ∈ right.support,
          rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧
        RlcBookRightIntersectionRankRealizedAt gamma right ∧
        RlcBookRightIntersectionRankMinimalAt gamma gamma' right ∧
        RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
          gamma gamma' omega c hx hy ∧
        ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
        ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
  obtain ⟨z, x, y, u, right, flipLeft, c, hx, hy,
      hcycle, hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder,
      hflipLeftRank, hfirst,
      hrankRealized, hglobalMin,
      hclassified, hxPlace, hyPlace⟩ :=
    rlc_twoChannelFullPhysical_firstIntersection_twoArcClassified_of_noGood
      gamma gamma' hfaith omega hno hnoGood
  have hbad :=
    rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified
      hno hnoGood c hx hy hxPath hyPath hclassified
  exact ⟨z, x, y, u, right, flipLeft, c, hx, hy,
    hcycle, hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder,
    hflipLeftRank, hfirst,
    hrankRealized, hglobalMin,
    hbad, hxPlace, hyPlace⟩


end
end StatMech.Universality
