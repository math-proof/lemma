/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

abbrev RlcTwoChannelIndexedOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  RlcConnectorVertex n ⊕
    ((Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') × Bool) ⊕
      Ising.kwg_Face
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))

end
end StatMech.Universality
