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
import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part18


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

theorem affineResidualNonneg_absSum_le_radius_zero :
    (RatInterval.VectorAbsSum
      (RatInterval.matrixVectorAffineResidualNonneg intervals offsetIntervals
        (RatInterval.pointVector centerQ) intervals_nonnegative
        (RatInterval.pointVector_nonnegative centerQ_nonnegative)) : ℝ) ≤
      (1 - (columnSumContraction.c : ℝ)) * (0 : ℝ) := by
  norm_num [RatInterval.VectorAbsSum,
    RatInterval.matrixVectorAffineResidualNonneg,
    RatInterval.matrixVectorAffineNonneg,
    RatInterval.matrixVectorMulNonneg,
    RatInterval.pointVector, RatInterval.pointMatrix, RatInterval.finsetSum,
    RatInterval.vectorSub, RatInterval.vectorAdd, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mulNonneg,
    RatInterval.point, RatInterval.absUpper, intervals, offsetIntervals,
    matrixQ, offsetQ, centerQ, columnSumContraction]


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
