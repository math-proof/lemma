/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificateExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificateExample.Part3


namespace StatMech

namespace Exact3D

namespace MatrixCertificateExample

noncomputable def stableColumnClosedBallCertificate :
    FiniteContraction.ClosedBallContractionCertificate
      (fun x i => RatInterval.matVec stableMatrix x i) :=
  FiniteContraction.closedBallContractionCertificate_of_columnSumContraction_and_rationalCenter
    stablePointMatrixColumnSumContraction stableMatrix_mem_pointMatrix
    stableCenterQ (radius := 0) (by norm_num) (by
      rw [stableRationalResidual_absSum_zero]
      norm_num)


end MatrixCertificateExample
end Exact3D
end StatMech
