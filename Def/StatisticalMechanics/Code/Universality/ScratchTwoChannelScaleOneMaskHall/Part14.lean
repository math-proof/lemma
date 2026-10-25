/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part8


namespace StatMech.Universality

noncomputable def rlcScaleOneConnectorFailureEmbedding :
    RlcScaleOneConnectorFailure ↪ RlcScaleOneConnectorSuccessConfig where
  toFun rho :=
    ⟨rlcScaleOneTaggedTarget (rlcScaleOneFailureClassify rho),
      rlcScaleOneTaggedTarget_connectorSuccess
        (rlcScaleOneFailureClassify rho)⟩
  inj' rho rho' h := by
    apply rlcScaleOneFailureClassifyEmbedding.injective
    apply rlcScaleOneTaggedTargetEmbedding.injective
    exact congrArg Subtype.val h


end StatMech.Universality
