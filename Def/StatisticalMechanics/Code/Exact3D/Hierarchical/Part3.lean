module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
public import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
public import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

def hierarchicalStableRowSumContraction :
    RatInterval.RowSumContraction hierarchicalStableLinearizationIntervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i
    norm_num [RatInterval.MatrixAbsRowSum, hierarchicalStableLinearizationIntervals,
      RatInterval.point, RatInterval.absUpper]


end Exact3D
end StatMech
