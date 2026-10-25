/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part39
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFaithfulForcedDualEdgeEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) : Real :=
  ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
    A.indicator (fun _ => (1 : Real))
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
      rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega


end
end StatMech.Universality
