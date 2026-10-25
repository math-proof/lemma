/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall


namespace StatMech.Universality

noncomputable def rlcScaleOneSectionBList : List RlcScaleOneSectionB :=
  (Finset.univ.filter fun w =>
    rlcScaleOneSectionBAvoidsSelectedRoutes w = true).toList

noncomputable def rlcScaleOneSectionCList : List RlcScaleOneSectionC :=
  (Finset.univ.filter fun w =>
    rlcScaleOneSectionCAvoidsSelectedRoutes w = true).toList

end StatMech.Universality
