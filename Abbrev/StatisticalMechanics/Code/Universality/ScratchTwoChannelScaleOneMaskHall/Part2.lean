/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall


namespace StatMech.Universality

abbrev RlcScaleOnePairBlockFailure :=
  {w : RlcScaleOnePairBlock // rlcScaleOnePairBlockAvoidsRoute w = true}

abbrev RlcScaleOneFiveBlockFailure :=
  {w : RlcScaleOneFiveBlock // rlcScaleOneFiveBlockAvoidsRoutes w = true}

abbrev RlcScaleOneSectionAFactors :=
  RlcScaleOnePairBlockFailure × RlcScaleOneFiveBlockFailure ×
    RlcScaleOneFiveBlockFailure × RlcScaleOneUnusedBlock

end StatMech.Universality
