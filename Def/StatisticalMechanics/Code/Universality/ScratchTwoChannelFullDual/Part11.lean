/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFullOuterOnRight {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (x : RlcTwoChannelFullOuterVertex n) : Prop :=
  (x : Site 2) ∈ rlc_pathVertices gamma.1

def rlc_twoChannelFullOuterOnLeft {n : Int}
    (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelFullOuterVertex n) : Prop :=
  (x : Site 2) ∈ rlc_pathVertices gamma'.1


def rlc_twoChannelFullOuterConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcTwoChannelFullOuterVertex n))) :=
  {eta | ∃ x y : RlcTwoChannelFullOuterVertex n,
    rlc_twoChannelFullOuterOnRight gamma x ∧
      rlc_twoChannelFullOuterOnLeft gamma' y ∧
      (FK.openSub (rlc_twoChannelFullOuterGraph n) eta).Reachable x y}

end
end StatMech.Universality
