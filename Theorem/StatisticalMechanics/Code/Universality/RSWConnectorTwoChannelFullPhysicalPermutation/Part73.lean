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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part72
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contactCycleCertificate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hcertificate : RlcTwoChannelFullPhysicalContactCycleCertificate
      gamma gamma' omega) :
    RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
  obtain ⟨x, y, u, c, hx, hy, hcycle, hxPath, hyPath, hplace⟩ :=
    hcertificate
  apply rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcSide
    c hx hy hxPath hyPath
  exact
    (rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc
      gamma gamma' omega c hcycle.isTrail hx hy).2 hplace


theorem rlc_twoChannelFullPhysicalGoodComponentContacts_of_contactCycleCertificate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hcertificate : RlcTwoChannelFullPhysicalContactCycleCertificate
      gamma gamma' omega) :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
  obtain ⟨x, y, u, c, hx, hy, hcycle, hxPath, hyPath, hplace⟩ :=
    hcertificate
  apply rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide
    gamma gamma' omega c hx hy hxPath hyPath
  exact
    (rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc
      gamma gamma' omega c hcycle.isTrail hx hy).2 hplace


theorem rlc_twoChannelFullPhysicalContactCycleCertificate_of_goodComponent
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hcomponent : RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    RlcTwoChannelFullPhysicalContactCycleCertificate
      gamma gamma' omega := by
  obtain ⟨x, y, hxy, hxPath, hyPath⟩ := hcomponent
  have hxyNe : x ≠ y := by
    intro hEq
    subst y
    exact (Finset.disjoint_left.mp hfaith.exposed_disjoint)
      hxPath hyPath
  obtain ⟨pGood⟩ := hxy
  let pGoodPath : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x y := pGood.toPath
  have hpGoodPath : pGoodPath.IsPath := pGood.toPath.property
  let p := pGoodPath.mapLe
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)
  have hpPath : p.IsPath := hpGoodPath.mapLe _
  have hpNonNil : ¬p.Nil := p.not_nil_of_ne hxyNe
  have hxSupport : x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    (p.adj_snd hpNonNil).mem_support_left
  have hySupport : y ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    (p.adj_penultimate hpNonNil).mem_support_right
  obtain ⟨u, c, hc, hx, hy⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts
      gamma gamma' omega hxSupport hySupport
  have harc := rlc_isCycles_isPath_eq_ordered_or_complementary
    (rlc_twoChannelFullFilledBoundary_isCycles gamma gamma' omega)
    c hc hx hy hxyNe p hpPath
  have hpCarried : ∀ {f g : Site 2}, s(f, g) ∈ p.edges →
      RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' f g := by
    intro f g hfg
    have hfgGood : s(f, g) ∈ pGoodPath.edges := by
      simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfg
    exact
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
        gamma gamma' omega).1 (pGoodPath.adj_of_mem_edges hfgGood) |>.2
  have hside : RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy := by
    rcases harc with hpOrd | hpComp
    · left
      intro f g hfg
      apply hpCarried
      simpa [hpOrd] using hfg
    · right
      intro f g hfg
      apply hpCarried
      simpa [hpComp] using hfg
  exact ⟨x, y, u, c, hx, hy, hc, hxPath, hyPath,
    (rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc
      gamma gamma' omega c hc.isTrail hx hy).1 hside⟩


end
end StatMech.Universality
