/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall


namespace StatMech.Universality

def rlcScaleOnePairBlockAvoidsRoute (w : RlcScaleOnePairBlock) : Bool :=
  !(w 0 && w 1)

def rlcScaleOneFiveBlockAvoidsRoutes (w : RlcScaleOneFiveBlock) : Bool :=
  !(w 4 && w 0 && w 1) && !(w 4 && w 2 && w 3)

end StatMech.Universality
