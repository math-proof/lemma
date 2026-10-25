/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

theorem stableIntervals_eq_pointMatrix :
    stableIntervals = RatInterval.pointMatrix stableMatrixQ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stableIntervals, stableMatrixQ, RatInterval.pointMatrix,
      RatInterval.point]


theorem stableMatrix_eq_rational :
    stableMatrix = fun i j => (stableMatrixQ i j : ℝ) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [stableMatrix, stableMatrixQ]


theorem stableMatrix_mem_intervals :
    RatInterval.MatrixMem stableMatrix stableIntervals := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stableMatrix, stableIntervals, RatInterval.point, RatInterval.MemR]


theorem stableMatrix_mem_pointMatrix :
    RatInterval.MatrixMem stableMatrix (RatInterval.pointMatrix stableMatrixQ) := by
  rw [stableMatrix_eq_rational]
  exact RatInterval.pointMatrix_memR stableMatrixQ


end MatrixCertificateExample
end Exact3D
end StatMech
