/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part2


namespace StatMech.Universality

def rlcScaleOneSectionAAvoidsSelectedRoutes (w : RlcScaleOneSectionA) : Bool :=
  rlcScaleOnePairBlockAvoidsRoute ![w 6, w 7] &&
  rlcScaleOneFiveBlockAvoidsRoutes ![w 0, w 1, w 2, w 3, w 4] &&
  rlcScaleOneFiveBlockAvoidsRoutes ![w 10, w 11, w 13, w 14, w 9]

def rlcScaleOneSectionBAvoidsSelectedRoutes (w : RlcScaleOneSectionB) : Bool :=
  !(w 0 && w 1 && w 4) &&
  !(w 6 && w 7 && w 10) &&
  !(w 8 && w 11 && w 12) &&
  !(w 2 && w 3 && w 4) &&
  !(w 8 && w 9 && w 10) &&
  !(w 5 && w 7 && w 10) &&
  !(w 3 && w 4 && w 5)

def rlcScaleOneSectionCAvoidsSelectedRoutes (w : RlcScaleOneSectionC) : Bool :=
  !(w 7 && w 8) &&
  !(w 0 && w 1 && w 4) &&
  !(w 2 && w 3 && w 4) &&
  !(w 7 && w 10 && w 11) &&
  !(w 3 && w 4 && w 5) &&
  !(w 3 && w 4 && w 6)

end StatMech.Universality
