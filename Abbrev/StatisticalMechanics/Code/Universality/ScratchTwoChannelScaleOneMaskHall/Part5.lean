/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part7


namespace StatMech.Universality

abbrev RlcScaleOneFiberA :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 0 ∧
      rlcScaleOneSectionAAvoidsSelectedRoutes
        (rlcScaleOneRestrictA omega) = true}

abbrev RlcScaleOneFiberB :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 1 ∧
      rlcScaleOneSectionBAvoidsSelectedRoutes
        (rlcScaleOneRestrictB omega) = true}

abbrev RlcScaleOneFiberC :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 2 ∧
      rlcScaleOneSectionCAvoidsSelectedRoutes
        (rlcScaleOneRestrictC omega) = true}

abbrev RlcScaleOneFiberD :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 3 ∧ omega 2 = false ∧
      omega 5 = false ∧ omega 6 = true ∧ omega 8 = false}

end StatMech.Universality
