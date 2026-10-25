/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part5


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def toClosedBallCertificateOfFiniteResidualVector
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    (B.finiteResidual_le_of_vectorMem center hfiniteResidualMem)
    htail hbudget

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
