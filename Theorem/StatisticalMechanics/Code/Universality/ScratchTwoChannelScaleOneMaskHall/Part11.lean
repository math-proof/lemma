/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part14


namespace StatMech.Universality

theorem rlcScaleOneFiberA_reservedBit_not_pointwise :
    ∃ rho sigma : RlcScaleOneFiberA, rho.1 7 ≠ sigma.1 7 := by
  let rho : RlcScaleOneFiberA := ⟨fun _ => false, by decide⟩
  let sigma : RlcScaleOneFiberA :=
    ⟨fun i => decide (i = (7 : Fin 16)), by decide⟩
  exact ⟨rho, sigma, by simp [rho, sigma]⟩

#print axioms rlcScaleOneConnectorFailureEmbedding
#print axioms rlcScaleOneFiberA_reservedBit_not_pointwise

end StatMech.Universality
