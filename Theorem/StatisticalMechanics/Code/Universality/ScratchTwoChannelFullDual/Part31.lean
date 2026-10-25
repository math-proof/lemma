/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part39
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullMaxOuterContraction_eq_of_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullMaxOutsideGraph gamma gamma').Reachable x y) :
    rlc_twoChannelFullMaxOuterContraction gamma gamma' x =
      rlc_twoChannelFullMaxOuterContraction gamma gamma' y :=
  ConnectedComponent.sound hxy

theorem rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj x y) :
    rlc_twoChannelFullMaxInnerContraction gamma gamma' x =
      rlc_twoChannelFullMaxInnerContraction gamma gamma' y := by
  exact rlc_twoChannelFullMaxOuterContraction_eq_of_reachable
    gamma gamma' hxy.2

end
end StatMech.Universality
