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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelFullPhysicalSuccessEmbedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess
      gamma gamma' hfaith) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' where
  toFun rho := ⟨rlc_twoChannelFullPhysicalPermConfig gamma gamma' rho.1,
    hphysical rho⟩
  inj' := by
    intro rho sigma h
    apply Subtype.ext
    apply rlc_twoChannelFullPhysicalPermConfig_injective
    exact congrArg (fun eta : RlcTwoChannelEdgeSuccess gamma gamma' => eta.1) h

end
end StatMech.Universality
