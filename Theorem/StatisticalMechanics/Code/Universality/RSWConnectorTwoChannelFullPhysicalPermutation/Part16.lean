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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalVisibleCutDuality_of_staticCutConnectivity
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutConnectivity
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalVisibleCutDuality gamma gamma' hfaith := by
  intro omega hno
  let A := rlc_twoChannelFullPhysicalVisibleRightReachSet
    gamma gamma' omega
  obtain ⟨x, y, hx, hy, hxy⟩ := hstatic A
    (fun _ hx =>
      rlc_twoChannelFullPhysical_right_mem_visibleRightReachSet omega hx)
    (fun _ hy =>
      rlc_twoChannelFullPhysical_left_not_mem_visibleRightReachSet_of_failure
        omega hno hy)
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [rlc_twoChannelFullPhysicalVisibleCutTargetGraph, A] using hxy

theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_visibleCutDuality
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hduality : RlcTwoChannelFullPhysicalVisibleCutDuality
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
  intro rho
  exact rlc_twoChannelFullPhysicalPermConfig_success_of_visibleCutTarget
    rho.1 (hduality rho.1 rho.2)

theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hintersect : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith :=
  rlc_twoChannelFullPhysicalPermutationSuccess_of_visibleCutDuality hfaith
    (rlc_twoChannelFullPhysicalVisibleCutDuality_of_staticCutConnectivity
      hfaith
      (rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection
        hfaith hintersect))

theorem rlc_twoChannelFullVariableFailureDuality_of_visibleCutDuality
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hduality : RlcTwoChannelFullPhysicalVisibleCutDuality
      gamma gamma' hfaith) :
    RlcTwoChannelFullVariableFailureDuality gamma gamma' hfaith := by
  intro omega hno
  exact rlc_twoChannelFullVariableConnectorSuccess_of_visibleCutTarget
    omega (hduality omega hno)


end
end StatMech.Universality
