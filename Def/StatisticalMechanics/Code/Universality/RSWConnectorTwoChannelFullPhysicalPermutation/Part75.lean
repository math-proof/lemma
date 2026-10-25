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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part75
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullPhysicalUnrepairableTerminalProductObstruction
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Prop :=
  ∃ (z x y u : Site 2)
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk
      z (gamma'.1.2.1 : Site 2))
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (ur vr ul vl : Site 2)
    (qRepairR : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (qRepairL : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
    (rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
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
      rlc_orderedContourArc c hx hy =
        (qRepairR.mapLe
          (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
            gamma gamma' omega)).append (.cons hurv rr) ∧
      (rlc_complementaryContourArc c hx hy).reverse =
        (qRepairL.mapLe
          (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le
            gamma gamma' omega)).append (.cons hulv rl) ∧
      rr.length < (rlc_orderedContourArc c hx hy).length ∧
      rl.length <
        (rlc_complementaryContourArc c hx hy).reverse.length ∧
      ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Reachable ur vr ∧
      ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Reachable ul vl ∧
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' ur vr ∧
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' ul vl ∧
      RlcTwoChannelFullPhysicalRightArcClassifiedBad
        gamma gamma' omega ur vr ∧
      RlcTwoChannelFullPhysicalLeftArcClassifiedBad
        gamma gamma' omega ul vl ∧
      RlcTwoChannelFullPhysicalWallTerminalProductClassification
          gamma gamma' omega (vr := vr) (vl := vl) qr ql ∧
      ((∃ e ∈ qr.edges,
          Sym2.map rlc_dualReflect e ∉
            rlc_connectorFourTraceEdges gamma gamma') ∨
        (∃ e ∈ ql.edges,
          Sym2.map rlc_dualReflect e ∉
            rlc_connectorFourTraceEdges gamma gamma') ∨
        RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad
          gamma gamma' omega ur vr ∨
        RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad
          gamma gamma' omega ul vl ∨
        (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable
            gamma gamma' omega qr ql ∧
          RlcTwoChannelFullPhysicalOrderedWallFamilyOutcome
            gamma gamma' omega flipLeft qr ql)) ∧
      ((∃ e ∈ qr.edges,
          Sym2.map rlc_dualReflect e ∉
            rlc_connectorFourTraceEdges gamma gamma') ∨
        (∃ e ∈ ql.edges,
          Sym2.map rlc_dualReflect e ∉
            rlc_connectorFourTraceEdges gamma gamma') ∨
        RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad
          gamma gamma' omega ur vr ∨
        RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad
          gamma gamma' omega ul vl ∨
        RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows
          gamma gamma' omega flipLeft qr ql)


end
end StatMech.Universality
