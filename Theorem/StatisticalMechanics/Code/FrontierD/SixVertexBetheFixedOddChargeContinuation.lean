/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddChargeContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedOddChargeBetheParticleCount_eq (s k : Nat) :
    sixVertexFixedChargeBetheParticleCount (2 * s + 1) k =
      ((s + k + 1) + 1) + (s + k + 1) := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega

end
end StatMech.FrontierD
