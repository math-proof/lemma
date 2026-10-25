/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairCompletionProfile
    (T : EvenTorus)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (sixVertexHorizontalCompletionProfile T horizontal.1,
    sixVertexHorizontalCompletionProfile T horizontal.2)

def sixVertexHorizontalPairProfileChooseWeight
    {T : EvenTorus} (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  sixVertexHorizontalProfileChooseCount left profile.1 *
    sixVertexHorizontalProfileChooseCount right profile.2

end
end StatMech.FrontierD
