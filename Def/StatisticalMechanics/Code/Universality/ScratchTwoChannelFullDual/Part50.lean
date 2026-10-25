/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part41
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def rlc_twoChannelFaithfulFaceOnRight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : RlcTwoChannelFaithfulFace gamma gamma') : Prop :=
  ∃ x : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧
    C = BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)

def rlc_twoChannelFaithfulFaceOnLeft {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : RlcTwoChannelFaithfulFace gamma gamma') : Prop :=
  ∃ x : RlcConnectorVertex n, rlc_connectorOnLeft gamma' x ∧
    C = BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)

end
end StatMech.Universality
