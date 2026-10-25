/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFacePIMSConfig_congr_of_centralEdges {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {rho sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hcentral : ∀ (e : Sym2 (Site 2))
      (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma'),
      rho (rlc_connectorCentralFaceEdgeLift e he) =
        sigma (rlc_connectorCentralFaceEdgeLift e he)) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho =
      rlc_connectorCentralFacePIMSConfig gamma gamma' sigma := by
  funext target
  rw [rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFacePIMSConfig_apply]
  unfold rlc_connectorCentralFaceAmbientConfig
  split
  · rename_i he
    rw [hcentral _ he]
  · rfl


end
end StatMech.Universality
