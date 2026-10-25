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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part63
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceSegmentCases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases
      gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
    RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases
      gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
  rcases h with hEq | hEarlier | hLater | hBoth
  · exact Or.inl hEq
  · exact Or.inr (Or.inl
      ⟨rlc_twoChannelFullPhysical_wallFamilyRowTwo_earlierTraceSegment
          hzCandidate hEarlier.1,
        hEarlier.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨hLater.1,
        rlc_twoChannelFullPhysical_wallFamilyRowTwo_laterTraceSegment
          hzCandidate hLater.2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨rlc_twoChannelFullPhysical_wallFamilyRowTwo_earlierTraceSegment
          hzCandidate hBoth.1,
        rlc_twoChannelFullPhysical_wallFamilyRowTwo_laterTraceSegment
          hzCandidate hBoth.2⟩))


end
end StatMech.Universality
