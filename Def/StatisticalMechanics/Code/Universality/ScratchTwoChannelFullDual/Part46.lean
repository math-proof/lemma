/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part37
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelFaithfulForcedDualEdgeZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
    BeffaraDC.pfdDualWeight
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))


end
end StatMech.Universality
