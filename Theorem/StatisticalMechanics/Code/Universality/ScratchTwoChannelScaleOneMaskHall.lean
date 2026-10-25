/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part3


namespace StatMech.Universality

theorem rlcScaleOnePairBlockFailure_card :
    Fintype.card RlcScaleOnePairBlockFailure = 3 := by
  decide

theorem rlcScaleOneFiveBlockFailure_card :
    Fintype.card RlcScaleOneFiveBlockFailure = 25 := by
  decide

theorem rlcScaleOneSectionAFailure_card :
    Fintype.card RlcScaleOneSectionAFailure = 15000 := by
  rw [Fintype.card_congr rlcScaleOneSectionAFactorEquiv]
  simp only [RlcScaleOneSectionAFactors, Fintype.card_prod,
    rlcScaleOnePairBlockFailure_card, rlcScaleOneFiveBlockFailure_card,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem rlcScaleOneSectionBFailure_card :
    Fintype.card RlcScaleOneSectionBFailure = 3941 := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem rlcScaleOneSectionCFailure_card :
    Fintype.card RlcScaleOneSectionCFailure = 2002 := by
  decide

end StatMech.Universality
