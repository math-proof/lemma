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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullVariableFailureDuality_of_visiblePlanarDuality
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hplanar : RlcTwoChannelFullPhysicalVisiblePlanarDuality
      gamma gamma' hfaith) :
    RlcTwoChannelFullVariableFailureDuality gamma gamma' hfaith := by
  intro omega hno
  exact hplanar omega
    (rlc_twoChannelFullPhysical_not_visibleSourceConnector_of_failure
      omega hno)

theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_visiblePlanarDuality
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hplanar : RlcTwoChannelFullPhysicalVisiblePlanarDuality
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
  intro rho
  apply rlc_twoChannelFullPhysicalPermConfig_success_of_variableConnector
  exact hplanar rho.1
    (rlc_twoChannelFullPhysical_not_visibleSourceConnector_of_failure
      rho.1 rho.2)

theorem rlc_twoChannelFullPhysicalPermutationSuccess_of_variableFailureDuality
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hduality : RlcTwoChannelFullVariableFailureDuality
      gamma gamma' hfaith) :
    RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
  intro rho
  exact rlc_twoChannelFullPhysicalPermConfig_success_of_variableConnector
    rho.1 (hduality rho.1 rho.2)


end
end StatMech.Universality
