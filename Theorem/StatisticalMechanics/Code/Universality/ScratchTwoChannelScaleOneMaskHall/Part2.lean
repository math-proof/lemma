/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part4


namespace StatMech.Universality

theorem rlcScaleOneSectionBList_mem (w : RlcScaleOneSectionB) :
    w ∈ rlcScaleOneSectionBList ↔
      rlcScaleOneSectionBAvoidsSelectedRoutes w = true := by
  rw [rlcScaleOneSectionBList, Finset.mem_toList, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem rlcScaleOneSectionCList_mem (w : RlcScaleOneSectionC) :
    w ∈ rlcScaleOneSectionCList ↔
      rlcScaleOneSectionCAvoidsSelectedRoutes w = true := by
  rw [rlcScaleOneSectionCList, Finset.mem_toList, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

end StatMech.Universality
