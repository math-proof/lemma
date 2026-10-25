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
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part22


namespace StatMech

namespace Exact3D

open scoped NNReal

namespace FiniteContraction

namespace ZeroLinearExample

noncomputable def closedBallCertificate {radius : ℝ} (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec matrix x i) :=
  closedBallContractionCertificate_of_rowSumContraction_and_residualVector
    rowSumContraction matrix_mem_intervals (0 : Fin 1 → ℝ)
    (by norm_num [rowSumContraction]) hradius residual_mem (by
      simpa [RatInterval.VectorAbsSum, residualIntervals, RatInterval.point,
        RatInterval.absUpper, rowSumContraction] using hradius)


def centerQ : Fin 1 → ℚ :=
  fun _ => 0


noncomputable def rationalCenterClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate (fun x i => RatInterval.matVec matrix x i) :=
  closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter
    columnSumContraction matrix_mem_intervals centerQ hradius (by
      simpa [RatInterval.VectorAbsSum, RatInterval.matrixVectorResidual,
        RatInterval.matrixVectorMul, RatInterval.pointVector, RatInterval.finsetSum,
        RatInterval.vectorSub, RatInterval.sub, RatInterval.add, RatInterval.neg,
        RatInterval.mul, RatInterval.point, RatInterval.absUpper, centerQ,
        columnSumContraction] using hradius)


noncomputable def affineRationalCenterClosedBallCertificate {radius : ℝ}
    (hradius : 0 ≤ radius) :
    ClosedBallContractionCertificate
      (fun x i => RatInterval.affineMap matrix offset x i) :=
  closedBallContractionCertificate_of_columnSumContraction_affine_and_rationalCenter
    columnSumContraction matrix_mem_intervals offset_mem_intervals centerQ
    hradius (by
      simpa [RatInterval.VectorAbsSum, RatInterval.matrixVectorAffineResidual,
        RatInterval.matrixVectorAffine, RatInterval.matrixVectorMul,
        RatInterval.pointVector, RatInterval.finsetSum, RatInterval.vectorSub,
        RatInterval.vectorAdd, RatInterval.sub, RatInterval.add,
        RatInterval.neg, RatInterval.mul, RatInterval.point,
        RatInterval.absUpper, centerQ, offsetIntervals, columnSumContraction]
        using hradius)


end ZeroLinearExample
end FiniteContraction
end Exact3D
end StatMech
