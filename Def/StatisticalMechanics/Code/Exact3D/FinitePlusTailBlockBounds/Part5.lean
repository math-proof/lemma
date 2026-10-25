/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part4


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def toClosedBallCertificateOfComponentResiduals
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    FinitePlusTailClosedBallContractionCertificate n α :=
  B.toClosedBallCertificate hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    (B.residual_bound_of_componentResiduals center hfinite htail)
    (by simpa [add_assoc] using hbudget)

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
