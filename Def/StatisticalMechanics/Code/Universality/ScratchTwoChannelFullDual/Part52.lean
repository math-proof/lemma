/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part42
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFaithfulFaceConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (RlcTwoChannelFaithfulSourceEdge gamma gamma')) :=
  {eta | ∃ C D : RlcTwoChannelFaithfulFace gamma gamma',
    rlc_twoChannelFaithfulFaceOnRight gamma gamma' C ∧
    rlc_twoChannelFaithfulFaceOnLeft gamma gamma' D ∧
    (FK.indexedOpenGraph
      (rlc_twoChannelFaithfulEnds gamma gamma') eta).Reachable C D}


end
end StatMech.Universality
