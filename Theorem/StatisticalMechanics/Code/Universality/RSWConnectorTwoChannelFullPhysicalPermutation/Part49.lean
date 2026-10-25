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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part49
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad
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
    RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt
        gamma gamma' omega c hx hy ∧
      ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧
      ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
      hbadR, hdecR, hbadL, hdecL, hne⟩ :=
    rlc_twoChannelFullPhysical_twoArcFirstBad_of_not_contourArcSide
      gamma gamma' omega c hc hx hy hbadSide
  have hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hxPath]
  have hyBarrier : rlc_dualReflect y ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hyPath]
  have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using
      (rlc_rightPathVertex_mem_connectorBox gamma hxPath)
  have hyBox : rlc_dualReflect y ∈ rlc_connectorBox n := by
    simpa [rlc_connectorBox] using
      (rlc_leftPathVertex_mem_connectorBox gamma' hyPath)
  have hclassR :
      ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
          gamma gamma' ur vr) ∧
        (rlc_dualReflect ur ∈ rlc_connectorBarrier gamma gamma' ∨
          (rlc_dualReflect ur) 0 = -2 * n ∨
          (rlc_dualReflect ur) 0 = 2 * n ∨
          (rlc_dualReflect ur) 1 = -n ∨
          (rlc_dualReflect ur) 1 = n)) ∨
      ∃ p q : Site 2,
        sharedPrimalEdge ur vr = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          (p ∈ rlc_connectorBarrier gamma gamma' ∨
            p 0 = -2 * n ∨ p 0 = 2 * n ∨
            p 1 = -n ∨ p 1 = n) := by
    rcases rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
        gamma gamma' omega hurv hbadR with htarget | hsource
    · exact Or.inl ⟨htarget,
        rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
          hxBarrier hxBox qr hurv htarget⟩
    · exact Or.inr
        (rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
          gamma gamma' omega hurv hsource)
  have hclassL :
      ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
          gamma gamma' ul vl) ∧
        (rlc_dualReflect ul ∈ rlc_connectorBarrier gamma gamma' ∨
          (rlc_dualReflect ul) 0 = -2 * n ∨
          (rlc_dualReflect ul) 0 = 2 * n ∨
          (rlc_dualReflect ul) 1 = -n ∨
          (rlc_dualReflect ul) 1 = n)) ∨
      ∃ p q : Site 2,
        sharedPrimalEdge ul vl = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
          (p ∈ rlc_connectorBarrier gamma gamma' ∨
            p 0 = -2 * n ∨ p 0 = 2 * n ∨
            p 1 = -n ∨ p 1 = n) := by
    rcases rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
        gamma gamma' omega hulv hbadL with htarget | hsource
    · exact Or.inl ⟨htarget,
        rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
          hyBarrier hyBox ql hulv htarget⟩
    · exact Or.inr
        (rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
          gamma gamma' omega hulv hsource)
  refine ⟨?_, hfaith.dualFace_rightContact_position hxPath,
    hfaith.dualFace_leftContact_position hyPath⟩
  exact ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
    hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL⟩


end
end StatMech.Universality
