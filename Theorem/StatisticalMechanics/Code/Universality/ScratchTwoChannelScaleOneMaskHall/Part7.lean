/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part10


namespace StatMech.Universality

theorem rlcScaleOneTaggedTarget_success (rho : RlcScaleOneRoutedFailure) :
    rlcScaleOneFourRouteSuccess (rlcScaleOneTaggedTarget rho) = true := by
  rcases rho with a | bcd
  · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberATarget,
      rlcScaleOneCodeAEmbedding, rlcScaleOneFourRouteSuccess,
      rlcScaleOneCodeA]
  · rcases bcd with b | cd
    · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberBTarget,
        rlcScaleOneCodeBEmbedding, rlcScaleOneFourRouteSuccess,
        rlcScaleOneCodeB]
    · rcases cd with c | d
      · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberCTarget,
          rlcScaleOneCodeCEmbedding, rlcScaleOneFourRouteSuccess,
          rlcScaleOneCodeC]
      · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberDTarget,
          rlcScaleOneCodeDEmbedding, rlcScaleOneFourRouteSuccess,
          rlcScaleOneCodeD]

end StatMech.Universality
