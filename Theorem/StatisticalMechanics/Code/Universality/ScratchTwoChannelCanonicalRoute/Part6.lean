/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPIMSConfig_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective (rlc_twoChannelFullPIMSConfig gamma gamma') := by
  intro rho sigma hfull
  funext e
  have happ : Bool.not (rho e) = Bool.not (sigma e) := by
    simpa only [rlc_twoChannelFullPIMSConfig,
      Equiv.apply_symm_apply] using
      congrFun hfull ((rlc_twoChannelPIMSEdgePerm gamma gamma').symm e)
  have hdouble := congrArg (fun b : Bool => !b) happ
  simpa using hdouble


end
end StatMech.Universality
