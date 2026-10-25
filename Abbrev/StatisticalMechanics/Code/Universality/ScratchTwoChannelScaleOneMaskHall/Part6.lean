/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part6


namespace StatMech.Universality

abbrev RlcScaleOneRoutedFailure :=
  RlcScaleOneFiberA ⊕ (RlcScaleOneFiberB ⊕
    (RlcScaleOneFiberC ⊕ RlcScaleOneFiberD))

end StatMech.Universality
