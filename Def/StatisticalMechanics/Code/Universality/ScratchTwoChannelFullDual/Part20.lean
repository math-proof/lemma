/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

noncomputable def rlc_twoChannelIndexedFaceProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' →
      Ising.kwg_Face
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
  | Sum.inl x => BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
  | Sum.inr (Sum.inl (f, false)) => BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inl (f, true)) => BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inr C) => C


end
end StatMech.Universality
