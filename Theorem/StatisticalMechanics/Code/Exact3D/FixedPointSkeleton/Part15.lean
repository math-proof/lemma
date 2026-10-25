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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part15


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

theorem matrix_mem_intervals : RatInterval.MatrixMem matrix intervals := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [matrix, matrixQ, intervals, RatInterval.pointMatrix,
    RatInterval.point, RatInterval.MemR]


theorem offset_mem_intervals : RatInterval.VectorMem offset offsetIntervals := by
  intro i
  fin_cases i
  norm_num [offset, offsetQ, offsetIntervals, RatInterval.pointVector,
    RatInterval.point, RatInterval.MemR]


theorem intervals_nonnegative : RatInterval.MatrixNonnegative intervals := by
  intro i j
  fin_cases i
  fin_cases j
  norm_num [intervals, RatInterval.pointMatrix, matrixQ, RatInterval.point,
    RatInterval.Nonnegative]


theorem centerQ_nonnegative (i : Fin 1) : 0 ≤ centerQ i := by
  fin_cases i
  norm_num [centerQ]


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
