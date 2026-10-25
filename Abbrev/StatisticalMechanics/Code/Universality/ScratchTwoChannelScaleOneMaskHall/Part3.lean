/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part2


namespace StatMech.Universality

abbrev RlcScaleOneSectionAFailure :=
  {w : RlcScaleOneSectionA // rlcScaleOneSectionAAvoidsSelectedRoutes w = true}

abbrev RlcScaleOneSectionBFailure :=
  {w : RlcScaleOneSectionB // rlcScaleOneSectionBAvoidsSelectedRoutes w = true}

abbrev RlcScaleOneSectionCFailure :=
  {w : RlcScaleOneSectionC // rlcScaleOneSectionCAvoidsSelectedRoutes w = true}

end StatMech.Universality
