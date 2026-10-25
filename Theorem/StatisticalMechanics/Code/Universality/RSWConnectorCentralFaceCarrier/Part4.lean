/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFaceRegionSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorCentralFaceRegionSet gamma gamma').Finite := by
  apply (rlc_connectorFaceBox n).finite_toSet.subset
  rintro f ⟨hf, _hs, _hreach⟩
  exact hf

end
end StatMech.Universality
