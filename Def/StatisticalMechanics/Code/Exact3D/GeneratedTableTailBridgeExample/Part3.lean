/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace GeneratedTableTailBridgeExample

noncomputable def keyImageIndicatorSplit {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key) :
    ContributionSplit α where
  finiteContribution := fun a => keyImageIndicator support classifier (classifier a)
  tailContribution := fun _ => 0
  totalContribution := fun a => keyImageIndicator support classifier (classifier a)


end GeneratedTableTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
