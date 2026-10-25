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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part15


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

def columnSumContraction : RatInterval.ColumnSumContraction intervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  col_bound := by
    intro j
    fin_cases j
    norm_num [RatInterval.MatrixAbsColSum, intervals, RatInterval.pointMatrix,
      matrixQ, RatInterval.absUpper, RatInterval.point]


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
