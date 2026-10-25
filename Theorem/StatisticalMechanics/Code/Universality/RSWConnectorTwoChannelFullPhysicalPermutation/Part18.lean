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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalSuccessEmbedding_compatible
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho
      (rlc_twoChannelFullPhysicalSuccessEmbedding hfaith hphysical rho) := by
  funext target
  let fullTarget := rlc_twoChannelPIMSVariableToFullPhysical target
  change rlc_twoChannelFullPhysicalPermConfig gamma gamma' rho.1 target.1 =
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 target.1
  calc
    _ = rlc_twoChannelFullDualConfig gamma gamma' rho.1 target.1.1 :=
      rlc_twoChannelFullPhysicalPermConfig_eq_fullDual rho.1 fullTarget
    _ = rlc_twoChannelPIMSEdgeProjection gamma gamma' rho.1 target.1 :=
      rlc_twoChannelFullDualConfig_variable_eq_projection rho.1 target
    _ = _ := by rw [← rlc_twoChannelPIMSEdgeTargetOfClosure_val]


end
end StatMech.Universality
