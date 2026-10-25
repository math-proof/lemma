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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part50
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
    (hallR : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hallL : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hurLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ur) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ur))
    (hulLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ul) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ul)) :
    RlcTwoChannelFullPhysicalTwoArcWallFamilyTruthTable
      gamma gamma' omega flipLeft qr ql := by
  have qrNotNil : ¬qr.Nil := by
    intro hnil
    have hxu : x = ur := hnil.eq
    rcases hurLoc with hurLeft | hurRight
    · exact hurLeft.2.2.1 (by simpa [← hxu] using hxPath)
    · exact hurRight.2.2.1 (by simpa [← hxu] using hxPath)
  have qlNotNil : ¬ql.Nil := by
    intro hnil
    have hyu : y = ul := hnil.eq
    rcases hulLoc with hulLeft | hulRight
    · exact hulLeft.2.2.2 (by simpa [← hyu] using hyPath)
    · exact hulRight.2.2.2 (by simpa [← hyu] using hyPath)
  rcases hurLoc with hurLeft | hurRight
  · have hqrLeft :=
      rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
        hfaith qr qrNotNil hallR hurLeft.2.1
    have hxz :=
      rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq
        right qr hxOrder hfirst hqrLeft hurLeft.2.1
    rcases hulLoc with hulLeft | hulRight
    · have hqlLeft :=
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
          hfaith ql qlNotNil hallL hulLeft.2.1
      have hyAxis :=
        rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis
          hfaith ql hyPath hqlLeft hulLeft.2.1
      exact Or.inl ⟨hqrLeft, hxz, hqlLeft, hyAxis⟩
    · have hqlRight :=
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
          hfaith ql qlNotNil hallL hulRight.2.1
      have hyReflected :=
        rlc_twoChannelFullPhysical_reflectedRightWalk_start
          ql hqlRight hulRight.2.1
      obtain ⟨r, hr, hyr⟩ := hyReflected
      have hrSuffix : r ∈ flipLeft.support := by
        rw [hyr] at hyOrder
        simpa using hyOrder
      exact Or.inr (Or.inl
        ⟨hqrLeft, hxz, hqlRight, r, hr, hyr, hrSuffix⟩)
  · have hqrRight :=
      rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
        hfaith qr qrNotNil hallR hurRight.2.1
    have hxAxis :=
      rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis
        hfaith qr hxPath hqrRight hurRight.2.1
    rcases hulLoc with hulLeft | hulRight
    · have hqlLeft :=
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
          hfaith ql qlNotNil hallL hulLeft.2.1
      have hyAxis :=
        rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis
          hfaith ql hyPath hqlLeft hulLeft.2.1
      exact Or.inr (Or.inr (Or.inl
        ⟨hqrRight, hxAxis, hqlLeft, hyAxis⟩))
    · have hqlRight :=
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
          hfaith ql qlNotNil hallL hulRight.2.1
      have hyReflected :=
        rlc_twoChannelFullPhysical_reflectedRightWalk_start
          ql hqlRight hulRight.2.1
      obtain ⟨r, hr, hyr⟩ := hyReflected
      have hrSuffix : r ∈ flipLeft.support := by
        rw [hyr] at hyOrder
        simpa using hyOrder
      exact Or.inr (Or.inr (Or.inr
        ⟨hqrRight, hxAxis, hqlRight, r, hr, hyr, hrSuffix⟩))


theorem rlc_twoChannelFullPhysical_twoArc_oppositeAxisWall_end_mem_suffixes_at
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur ul : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hqrRight : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hqlLeft : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) :
    ∃ (hzR : rlc_flipX z ∈
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
            rlc_flipXLatticeHom).dropUntil z hzL).support := by
  obtain ⟨hzR, hur⟩ :=
    rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at
      hnoGood z hzRight hzLeft qr hxAxis hqrRight
  obtain ⟨hzL, hul⟩ :=
    rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at
      hnoGood z hzRight hzLeft ql hyAxis hqlLeft
  exact ⟨hzR, hzL, hur, hul⟩


theorem rlc_connectorBarrier_original_or_exclusive_strict_reflected
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_connectorBarrier gamma gamma') :
    z ∈ rlc_pathVertices gamma.1 ∨
      z ∈ rlc_pathVertices gamma'.1 ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' z ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' z := by
  by_cases hzRight : z ∈ rlc_pathVertices gamma.1
  · exact Or.inl hzRight
  by_cases hzLeft : z ∈ rlc_pathVertices gamma'.1
  · exact Or.inr (Or.inl hzLeft)
  rcases rlc_connectorBarrier_original_or_strict_reflected
      gamma gamma' hz with hright | hleft | hflipLeft | hflipRight
  · exact False.elim (hzRight hright)
  · exact False.elim (hzLeft hleft)
  · exact Or.inr (Or.inr (Or.inl
      ⟨hflipLeft.1, hflipLeft.2, hzRight, hzLeft⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨hflipRight.1, hflipRight.2, hzRight, hzLeft⟩))


end
end StatMech.Universality
