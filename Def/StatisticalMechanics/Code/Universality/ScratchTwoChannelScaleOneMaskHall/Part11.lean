/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part7


namespace StatMech.Universality

def rlcScaleOneRouteMasks : List Nat :=
  [384, 19, 28, 196, 56, 224, 2816, 8960, 7168, 13312, 50176,
    2628, 8772, 344, 2656, 8800, 5760, 203, 54016, 2635, 8779,
    53828, 5720, 53856, 53835]

def RlcScaleOneRouteOpen (omega : RlcScaleOneEdgeConfig) (mask : Nat) : Prop :=
  ∀ i : Fin 16, mask.testBit i → omega i = true

def RlcScaleOneConnectorSuccess (omega : RlcScaleOneEdgeConfig) : Prop :=
  ∃ mask ∈ rlcScaleOneRouteMasks, RlcScaleOneRouteOpen omega mask

end StatMech.Universality
