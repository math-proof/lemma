/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part36
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFaithfulDualEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelEdgeConfig gamma gamma' ≃
      RlcTwoChannelEdgeConfig gamma gamma' where
  toFun := rlc_twoChannelFaithfulDualConfig gamma gamma'
  invFun := rlc_twoChannelFaithfulDualConfig gamma gamma'
  left_inv omega := by
    funext e
    simp [rlc_twoChannelFaithfulDualConfig]
  right_inv omega := by
    funext e
    simp [rlc_twoChannelFaithfulDualConfig]

end
end StatMech.Universality
