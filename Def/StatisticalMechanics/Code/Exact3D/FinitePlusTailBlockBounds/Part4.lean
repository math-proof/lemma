/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part3


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def toClosedBallCertificate
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  FinitePlusTailClosedBallContractionCertificate.ofResidualBound
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le)
    center hradius (by simpa using hresidual) (by simpa using hbudget)

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
