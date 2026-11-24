module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.Pi
public import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
public import Def.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part17


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FixedPointSkeleton.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace NonzeroAffineExample

theorem affineResidual_absSum_le_radius_one :
    (RatInterval.VectorAbsSum
      (RatInterval.matrixVectorAffineResidual intervals offsetIntervals
        (RatInterval.pointVector centerQ)) : ℝ) ≤
      (1 - (columnSumContraction.c : ℝ)) * (1 : ℝ) := by
  norm_num [RatInterval.VectorAbsSum, RatInterval.matrixVectorAffineResidual,
    RatInterval.matrixVectorAffine, RatInterval.matrixVectorMul,
    RatInterval.pointVector, RatInterval.pointMatrix, RatInterval.finsetSum,
    RatInterval.vectorSub, RatInterval.vectorAdd, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mul, RatInterval.point,
    RatInterval.absUpper, intervals, offsetIntervals, matrixQ, offsetQ,
    centerQ, columnSumContraction]


end NonzeroAffineExample
end FiniteContraction
end Exact3D
end StatMech
