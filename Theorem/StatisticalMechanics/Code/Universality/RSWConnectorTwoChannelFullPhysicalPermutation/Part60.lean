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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part60
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_exactOrderedWallTerminalRows
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (htable : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable
      gamma gamma' omega qr ql) :
    RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows
      gamma gamma' omega flipLeft qr ql := by
  rcases htable with hrow | hrow | hrow | hrow
  · have hxz :=
      rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq
        right qr hxOrder hfirst hrow.1 hrow.2.1.2.1
    have hyAxis :=
      rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis
        hfaith ql hyPath hrow.2.2.1 hrow.2.2.2.2.1
    refine Or.inl ⟨hrow, hxz, hyAxis, ?_⟩
    exact rlc_twoChannelFullPhysical_sameReflectedLeft_end_order
      hnoGood z hzRight hzLeft hxPath hyPath qr ql hxz hyAxis
        hrow.1 hrow.2.2.1 hrow.2.1 hrow.2.2.2
  · have hxz :=
      rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq
        right qr hxOrder hfirst hrow.1 hrow.2.1.2.1
    obtain ⟨r, hr, hyr⟩ :=
      rlc_twoChannelFullPhysical_reflectedRightWalk_start
        ql hrow.2.2.1 hrow.2.2.2.2.1
    have hrFlip : r ∈ flipLeft.support := by
      rw [hyr] at hyOrder
      simpa using hyOrder
    exact Or.inr (Or.inl ⟨hrow, hxz, r, hr, hyr, hrFlip⟩)
  · have hxAxis :=
      rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis
        hfaith qr hxPath hrow.1 hrow.2.1.2.1
    have hyAxis :=
      rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis
        hfaith ql hyPath hrow.2.2.1 hrow.2.2.2.2.1
    refine Or.inr (Or.inr (Or.inl ⟨hrow, hxAxis, hyAxis, ?_⟩))
    exact rlc_twoChannelFullPhysical_twoArc_oppositeAxisWall_end_mem_suffixes_at
      hnoGood hzRight hzLeft qr ql hxAxis hyAxis hrow.1 hrow.2.2.1
  · have hxAxis :=
      rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis
        hfaith qr hxPath hrow.1 hrow.2.1.2.1
    obtain ⟨r, hr, hyr⟩ :=
      rlc_twoChannelFullPhysical_reflectedRightWalk_start
        ql hrow.2.2.1 hrow.2.2.2.2.1
    have hrFlip : r ∈ flipLeft.support := by
      rw [hyr] at hyOrder
      simpa using hyOrder
    refine Or.inr (Or.inr (Or.inr ⟨r, hrow, hxAxis, hr, hyr,
      hrFlip, ?_⟩))
    exact rlc_twoChannelFullPhysical_sameReflectedRight_end_order
      hnoGood hr hxPath hyPath qr ql hxAxis hyr hrow.1 hrow.2.2.1
        hrow.2.1 hrow.2.2.2


end
end StatMech.Universality
