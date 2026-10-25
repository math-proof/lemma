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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part66
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (W : (hypercubicLattice 2).Walk ur ul),
      (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        (∀ v ∈ W.support,
          v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
        RlcTwoChannelFullPhysicalTetheredOrderedWallOrientationAlternative
          gamma gamma' omega flipLeft qr ql := by
  obtain ⟨ur, vr, ul, vl, qr, ql, W, hurv, hulv, hne, hWBox, hcases⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallOrientationCases
      hfaith right flipLeft hxPath hyPath hxOrder hyOrder hfirst hbad
  refine ⟨ur, vr, ul, vl, qr, ql, W, hurv, hulv, hne, hWBox, ?_⟩
  rcases hcases with hR | hL | hUr | hUl | ⟨hurLoc, hulLoc, htable⟩
  · exact Or.inl hR
  · exact Or.inr (Or.inl hL)
  · exact Or.inr (Or.inr (Or.inl hUr))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hUl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome
        hfaith hnoGood hzRight hzLeft hxPath hyPath flipLeft qr ql
          hurLoc hulLoc htable))))


theorem rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases_withDirections
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
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
        RlcTwoChannelFullPhysicalTetheredOrderedWallOrientationAlternative
          gamma gamma' omega flipLeft qr ql := by
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
        · have htable :=
            rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable
              hfaith right flipLeft qr ql hxPath hyPath hxOrder hyOrder
                hfirst hallR hallL hurLoc hulLoc
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome
              hfaith hnoGood hzRight hzLeft hxPath hyPath flipLeft qr ql
                hurLoc hulLoc htable))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hulLoc)))
      · exact Or.inr (Or.inr (Or.inl hurLoc))
    · exact Or.inr (Or.inl hallL)
  · exact Or.inl hallR


end
end StatMech.Universality
