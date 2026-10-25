/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalPairCompletionProfile (T : EvenTorus) :=
  Option (SixVertexHorizontalCompletionProfile T) ×
    Option (SixVertexHorizontalCompletionProfile T)

end
end StatMech.FrontierD
