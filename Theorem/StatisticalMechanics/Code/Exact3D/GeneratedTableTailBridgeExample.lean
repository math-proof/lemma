module
public import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridge.Part2
public import Def.StatisticalMechanics.Code.Exact3D.GeneratedTableTailBridgeExample
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/GeneratedTableTailBridgeExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace GeneratedTableTailBridgeExample

theorem zeroOneInterval_upper_le_one :
    ((zeroOneInterval.upper : ℚ) : ℝ) ≤ 1 := by
  norm_num [zeroOneInterval]


end GeneratedTableTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
