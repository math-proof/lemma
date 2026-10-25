/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFace_mem_faceBox {n : Int} (hn : 0 < n) :
    rlc_connectorCentralFace ∈ rlc_connectorFaceBox n := by
  simp [rlc_connectorCentralFace, rlc_connectorFaceBox, mem_rect]
  omega

end
end StatMech.Universality
