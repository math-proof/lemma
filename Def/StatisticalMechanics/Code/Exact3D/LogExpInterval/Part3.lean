module
public import Theorem.StatisticalMechanics.Code.Exact3D.LogExpBounds
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Theorem.StatisticalMechanics.Code.Exact3D.LogExpInterval.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpInterval.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace RatInterval

def divPositive (I J : RatInterval) (hJ : J.Positive) : RatInterval :=
  mul I (invPositive J hJ)


end RatInterval
end Exact3D
end StatMech
