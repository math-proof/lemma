/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.Pi
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part21


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ZeroLinearExample

def rowSumContraction : RatInterval.RowSumContraction intervals where
  c := 0
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i
    norm_num [RatInterval.MatrixAbsRowSum, intervals, RatInterval.point,
      RatInterval.absUpper]


def columnSumContraction : RatInterval.ColumnSumContraction intervals where
  c := 0
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  col_bound := by
    intro j
    fin_cases j
    norm_num [RatInterval.MatrixAbsColSum, intervals, RatInterval.point,
      RatInterval.absUpper]


def residualIntervals : RatInterval.IntervalVector 1 :=
  fun _ => RatInterval.point 0


end ZeroLinearExample
end FiniteContraction
end Exact3D
end StatMech
