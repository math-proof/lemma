/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Def.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample.Part2


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

theorem stableRationalResidual_memQ :
    RatInterval.VectorMemQ
      (fun i => (∑ j, stableMatrixQ i j * stableCenterQ j) - stableCenterQ i)
      (RatInterval.matrixVectorResidual (RatInterval.pointMatrix stableMatrixQ)
        (RatInterval.pointVector stableCenterQ)) :=
  RatInterval.matrixVectorResidual_memQ
    (RatInterval.pointMatrix_memQ stableMatrixQ)
    (RatInterval.pointVector_memQ stableCenterQ)


theorem stableRationalResidual_absSum_zero :
    RatInterval.VectorAbsSum
      (RatInterval.matrixVectorResidual (RatInterval.pointMatrix stableMatrixQ)
        (RatInterval.pointVector stableCenterQ)) = 0 := by
  norm_num [RatInterval.VectorAbsSum, RatInterval.matrixVectorResidual,
    RatInterval.matrixVectorMul, RatInterval.pointMatrix, RatInterval.pointVector,
    RatInterval.finsetSum, RatInterval.vectorSub, RatInterval.sub,
    RatInterval.add, RatInterval.neg, RatInterval.mul, RatInterval.point,
    RatInterval.absUpper, stableMatrixQ, stableCenterQ]


end MatrixCertificateExample
end Exact3D
end StatMech
