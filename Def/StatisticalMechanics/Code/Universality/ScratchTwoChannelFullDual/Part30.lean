/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part24
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFullInnerToVariable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma'))) :
    ConfigSpace (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet :=
  fun target => rho (rlc_twoChannelFullVariableTargetEdge_inner target).1

def rlc_twoChannelFullInnerOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' →
      RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  fun x => rlc_twoChannelIndexedOuterTarget gamma gamma' x.1

end
end StatMech.Universality
