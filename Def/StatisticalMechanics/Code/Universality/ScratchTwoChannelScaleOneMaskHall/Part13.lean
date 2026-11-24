module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
public import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

def rlcScaleOneFailureClassifyEmbedding :
    RlcScaleOneConnectorFailure ↪ RlcScaleOneRoutedFailure where
  toFun := rlcScaleOneFailureClassify
  inj' rho rho' h := by
    apply Subtype.ext
    have hconfig := congrArg rlcScaleOneRoutedFailureConfig h
    simpa only [rlcScaleOneFailureClassify_config] using hconfig

end StatMech.Universality
