/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part5


namespace StatMech.Universality

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rlcScaleOneSectionBList_length :
    rlcScaleOneSectionBList.length = 3941 := by
  unfold rlcScaleOneSectionBList
  rw [Finset.length_toList]
  exact rlcScaleOneSectionBFailure_card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rlcScaleOneSectionCList_length :
    rlcScaleOneSectionCList.length = 2002 := by
  unfold rlcScaleOneSectionCList
  rw [Finset.length_toList]
  exact rlcScaleOneSectionCFailure_card

end StatMech.Universality
