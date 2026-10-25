/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace GeneratedTableTailBridgeExample

theorem zeroOneInterval_memR_keyImageIndicator {α Key : Type*}
    [DecidableEq Key] (support : Finset α) (classifier : α → Key)
    (k : Key) :
    zeroOneInterval.MemR (keyImageIndicator support classifier k) := by
  by_cases hk : k ∈ support.image classifier
  · simp [keyImageIndicator, hk, zeroOneInterval, RatInterval.MemR]
  · simp [keyImageIndicator, hk, zeroOneInterval, RatInterval.MemR]


end GeneratedTableTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
