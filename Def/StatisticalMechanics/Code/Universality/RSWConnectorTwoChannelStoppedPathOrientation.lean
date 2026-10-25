/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part86
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedPathOrientation
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_stoppedTwoChannelOrientedCommonCycleState_of_noGood
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega) :
    RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega := by
  let H :=
    rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle
      gamma gamma' hfaith omega hno hnoGood
  let u := H.choose
  let c := H.choose_spec.choose
  have hspec := H.choose_spec.choose_spec
  exact ⟨S, u, c, hspec.1, hspec.2.1, hspec.2.2⟩


def RlcStoppedTwoChannelOrientedCandidateStateAt
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    (z : Site 2) : Prop :=
  z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧
    RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle
      gamma gamma' omega X.contour z


end
end StatMech.Universality
