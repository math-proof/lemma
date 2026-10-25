/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2


namespace StatMech.FrontierD

theorem sixVertexFourByTwo_locallyDegreeTwo :
    SixVertexLocallyDegreeTwo sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows := by
  intro v
  right
  rw [card_sixVertexLocalDisagreementSides]
  exact sixVertexFourByTwo_localDisagreementDegree_two v

end StatMech.FrontierD
