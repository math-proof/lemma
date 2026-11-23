/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG

@[expose] public section

namespace StatMech

namespace Exact3D

namespace IntervalLipschitzConstant

def zero : IntervalLipschitzConstant where
  interval := RatInterval.point 0
  nonnegative := by norm_num [RatInterval.point, RatInterval.Nonnegative]

end IntervalLipschitzConstant
end Exact3D
end StatMech
