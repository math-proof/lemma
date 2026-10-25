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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part59
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur ul : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hurLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ur) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ur))
    (hulLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ul) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ul))
    (h : RlcTwoChannelFullPhysicalTwoArcWallFamilyTruthTable
      gamma gamma' omega flipLeft qr ql) :
    RlcTwoChannelFullPhysicalOrderedWallFamilyOutcome
      gamma gamma' omega flipLeft qr ql := by
  rcases h with h | h | h | h
  · left
    refine ⟨h, ?_⟩
    have hurLeft :=
      rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location
        hfaith qr (Or.inl hxPath) h.1 hurLoc
    have hulLeft :=
      rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location
        hfaith ql (Or.inr hyPath) h.2.2.1 hulLoc
    exact rlc_twoChannelFullPhysical_sameReflectedLeft_end_order
      hnoGood z hzRight hzLeft hxPath hyPath qr ql h.2.1 h.2.2.2
        h.1 h.2.2.1 hurLeft hulLeft
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨h, ?_⟩))
    exact rlc_twoChannelFullPhysical_twoArc_oppositeAxisWall_end_mem_suffixes_at
      hnoGood hzRight hzLeft qr ql h.2.1 h.2.2.2 h.1 h.2.2.1
  · rcases h.2.2.2 with ⟨r, hr, hyr, hrFlip⟩
    have hurRight :=
      rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location
        hfaith qr (Or.inl hxPath) h.1 hurLoc
    have hulRight :=
      rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location
        hfaith ql (Or.inr hyPath) h.2.2.1 hulLoc
    refine Or.inr (Or.inr (Or.inr ⟨r, h.1, h.2.1, h.2.2.1,
      hr, hyr, hrFlip, ?_⟩))
    exact rlc_twoChannelFullPhysical_sameReflectedRight_end_order
      hnoGood hr hxPath hyPath qr ql h.2.1 hyr h.1 h.2.2.1
        hurRight hulRight


end
end StatMech.Universality
