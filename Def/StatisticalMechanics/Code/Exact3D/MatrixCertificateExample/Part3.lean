/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample.Part2


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

def stableRowSumContraction :
    RatInterval.RowSumContraction stableIntervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  row_bound := by
    intro i
    fin_cases i <;>
      norm_num [RatInterval.MatrixAbsRowSum, stableIntervals,
        RatInterval.point, RatInterval.absUpper]


def stablePointMatrixRowSumContraction :
    RatInterval.RowSumContraction (RatInterval.pointMatrix stableMatrixQ) :=
  RatInterval.rowSumContraction_of_pointMatrix stableMatrixQ
    (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1) (by
      intro i
      fin_cases i <;> norm_num [stableMatrixQ])


def stableColumnSumContraction :
    RatInterval.ColumnSumContraction stableIntervals where
  c := 1 / 2
  c_nonneg := by norm_num
  c_lt_one := by norm_num
  col_bound := by
    intro j
    fin_cases j <;>
      norm_num [RatInterval.MatrixAbsColSum, stableIntervals,
        RatInterval.point, RatInterval.absUpper]


def stablePointMatrixColumnSumContraction :
    RatInterval.ColumnSumContraction (RatInterval.pointMatrix stableMatrixQ) :=
  RatInterval.columnSumContraction_of_pointMatrix stableMatrixQ
    (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1) (by
      intro j
      fin_cases j <;> norm_num [stableMatrixQ])


end MatrixCertificateExample
end Exact3D
end StatMech
