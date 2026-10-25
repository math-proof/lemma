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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part62
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_earlierTraceSegment
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x : Site 2}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierContact
      gamma gamma' z x) :
    RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierTraceSegment
      gamma gamma' z x := by
  obtain ⟨r, hrSet, hxr, hrle, q, hqCandidate, hqr, hqz⟩ := h
  have hrPath : r ∈ rlc_pathVertices gamma.1 :=
    (Finset.mem_filter.mp hrSet).1
  have hzPath : z ∈ rlc_pathVertices gamma.1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hzCandidate).1).1
  have hrz : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by omega
  obtain ⟨P, hP⟩ :=
    rlc_rightAmbientTrace_segment_of_idxOf_le hrPath hzPath hrz
  exact ⟨r, q, P, hrSet, hxr, hrle, hqCandidate, hqr, hqz, hP⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_laterTraceSegment
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterContact
      gamma gamma' (z := z) (y := y) flipLeft) :
    RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterTraceSegment
      gamma gamma' (z := z) (y := y) flipLeft := by
  obtain ⟨s, hsPath, hys, hsSupport, hzs⟩ := h
  have hzPath : z ∈ rlc_pathVertices gamma.1 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hzCandidate).1).1
  obtain ⟨P, hP⟩ :=
    rlc_rightAmbientTrace_segment_of_idxOf_le hzPath hsPath (by omega)
  exact ⟨s, P, hsPath, hys, hsSupport, hzs, hP⟩


end
end StatMech.Universality
