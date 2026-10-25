/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelStoppedPathOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part86
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelStoppedPathOrientation.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcStoppedTwoChannelOrientedCandidateStateAt.resolved_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcStoppedTwoChannelCandidateResolved (G := G) omega tau := by
  exact Or.inr (hz.pims_success_of_failure X tau hno)


theorem RlcStoppedTwoChannelOrientedCommonCycleState.no_unresolved_candidate
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'} {hn : 0 < n}
    {hlt : G.lower + 1 < G.upper}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (X : RlcStoppedTwoChannelOrientedCommonCycleState G hn hlt omega)
    {z : Site 2}
    (hz : RlcStoppedTwoChannelOrientedCandidateStateAt X z)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    ¬(¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∧
      rlc_axisGapPIMSReflectedConfig G tau ∉
        rlc_finiteAxisGapConnectorEvent G) := by
  rintro ⟨_hnoGood, hnoSuccess⟩
  exact hnoSuccess (hz.pims_success_of_failure X tau hno)


theorem rlc_stoppedTwoChannel_good_or_pimsSuccess_of_failures
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (S : RlcStoppedExtremalAxisGapProvenance G hn hlt)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hnoTwoChannel : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hnoGap : tau ∉ rlc_finiteAxisGapConnectorEvent G) :
    RlcStoppedTwoChannelCandidateResolved (G := G) omega tau := by
  by_cases hgood : RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega
  · exact Or.inl hgood
  · let X := rlc_stoppedTwoChannelOrientedCommonCycleState_of_noGood
      G hn hlt S hfaith omega hnoTwoChannel hgood
    exact Or.inr (X.pims_success_of_failure tau hnoGap)

end
end StatMech.Universality
