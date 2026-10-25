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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part47
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_twoArcFirstBad_of_not_contourArcSide
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalTwoArcFirstBadAt
      gamma gamma' omega c hx hy := by
  let G := rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega
  let H := faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  let hord := rlc_orderedContourArc c hx hy
  let hcomp := rlc_complementaryContourArc c hx hy
  let hle : G ≤ H :=
    rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega
  have hnotOrd : ¬∀ {f g : Site 2}, s(f, g) ∈ hord.edges →
      RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
    intro h
    exact hbadSide (Or.inl h)
  have hnotComp : ¬∀ {f g : Site 2}, s(f, g) ∈ hcomp.edges →
      RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
    intro h
    exact hbadSide (Or.inr h)
  rcases rlc_walk_subgraph_lift_or_first_exit_decomp hle hord with
      ⟨q, hq⟩ | ⟨ur, vr, qr, rr, hurv, hurvBad, hdecompR⟩
  · exfalso
    apply hnotOrd
    intro f g hfg
    have hfg' : s(f, g) ∈ q.edges := by
      have hfgMap : s(f, g) ∈ (q.mapLe hle).edges := by
        rw [hq]
        exact hfg
      simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgMap
    exact
      ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).1 (q.adj_of_mem_edges hfg')).2
  · rcases rlc_walk_subgraph_lift_or_first_exit_decomp hle hcomp.reverse with
        ⟨q, hq⟩ | ⟨ul, vl, ql, rl, hulv, hulvBad, hdecompL⟩
    · exfalso
      apply hnotComp
      intro f g hfg
      have hfgRev : s(f, g) ∈ hcomp.reverse.edges := by
        simpa [SimpleGraph.Walk.edges_reverse] using hfg
      have hfg' : s(f, g) ∈ q.edges := by
        have hfgMap : s(f, g) ∈ (q.mapLe hle).edges := by
          rw [hq]
          exact hfgRev
        simpa only [SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgMap
      exact
        ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).1 (q.adj_of_mem_edges hfg')).2
    · have hurvCarrier :
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' ur vr := by
        intro hcarrier
        exact hurvBad
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨hurv, hcarrier⟩)
      have hulvCarrier :
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' ul vl := by
        intro hcarrier
        exact hulvBad
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨hulv, hcarrier⟩)
      have hurvEdge : s(ur, vr) ∈ hord.edges := by
        rw [hdecompR, SimpleGraph.Walk.edges_append]
        simp
      have hulvEdgeRev : s(ul, vl) ∈ hcomp.reverse.edges := by
        rw [hdecompL, SimpleGraph.Walk.edges_append]
        simp
      have hulvEdge : s(ul, vl) ∈ hcomp.edges := by
        simpa [SimpleGraph.Walk.edges_reverse] using hulvEdgeRev
      have hne : s(ur, vr) ≠ s(ul, vl) := by
        intro heq
        exact (rlc_orderedContourArc_edges_disjoint_complementary
          c hc hx hy) hurvEdge (by simpa [← heq] using hulvEdge)
      exact ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
        hurvCarrier, hdecompR, hulvCarrier, hdecompL, hne⟩


theorem rlc_twoChannelFullPhysical_faithful_twoArcFirstBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalTwoArcFirstBadAt
        gamma gamma' omega c hx hy ∧
      ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
      ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
  exact ⟨rlc_twoChannelFullPhysical_twoArcFirstBad_of_not_contourArcSide
      gamma gamma' omega c hc hx hy hbadSide,
    hfaith.dualFace_rightContact_position hxPath,
    hfaith.dualFace_leftContact_position hyPath⟩


end
end StatMech.Universality
