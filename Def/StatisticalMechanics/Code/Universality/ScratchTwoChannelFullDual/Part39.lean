/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullMaxOuterContraction {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' →
      RlcTwoChannelFullMaxOutsideComponent gamma gamma' :=
  (rlc_twoChannelFullMaxOutsideGraph gamma gamma').connectedComponentMk

noncomputable def rlc_twoChannelFullMaxInnerContraction {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' →
      RlcTwoChannelFullMaxOutsideComponent gamma gamma' :=
  fun x => rlc_twoChannelFullMaxOuterContraction gamma gamma'
    (rlc_twoChannelFullInnerOuterVertex gamma gamma' x)

end
end StatMech.Universality
