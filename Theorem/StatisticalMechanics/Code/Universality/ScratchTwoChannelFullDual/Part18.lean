/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part20
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelIndexedFaceProjection_outerEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    (rlc_twoChannelIndexedOuterEdge gamma gamma' f).map
        (rlc_twoChannelIndexedFaceProjection gamma gamma') =
      Ising.kwg_dualEnds
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f := by
  unfold rlc_twoChannelIndexedOuterEdge
  split
  · rename_i hret
    have hphysical := hret.choose_spec
    have hmapped := congrArg
      (Sym2.map (fun z : Site 2 => BeffaraDC.pfdFace
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm z))) hphysical
    simpa [rlc_twoChannelIndexedOuterTarget,
      rlc_twoChannelIndexedFaceProjection,
      rlc_twoChannelReflectedDualEdge, Ising.kwg_dualEnds,
      BeffaraDC.pfdFace, Sym2.map_map] using hmapped
  · simp [rlc_twoChannelIndexedOuterPort,
      rlc_twoChannelIndexedFaceProjection, Ising.kwg_dualEnds,
      BeffaraDC.pfdFace]

end
end StatMech.Universality
