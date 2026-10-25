/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridge.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace GeneratedTableTailBridgeExample

def zeroOneInterval : RatInterval where
  lower := 0
  upper := 1
  lower_le_upper := by norm_num


end GeneratedTableTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
