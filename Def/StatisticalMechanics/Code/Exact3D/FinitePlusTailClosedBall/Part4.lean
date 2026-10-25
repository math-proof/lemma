/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailClosedBall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part3


namespace StatMech

namespace Exact3D

open scoped NNReal


namespace FinitePlusTailClosedBallContractionCertificate

variable {n : ℕ} {α : Type*}


def with_larger_radius
    (C : FinitePlusTailClosedBallContractionCertificate n α)
    {radius' : ℝ} (hradius : C.radius ≤ radius') :
    FinitePlusTailClosedBallContractionCertificate n α where
  contraction := C.contraction
  center := C.center
  radius := radius'
  residual := C.residual
  radius_nonneg := le_trans C.radius_nonneg hradius
  residual_bound := C.residual_bound
  radius_bound := by
    have hmargin_nonneg : 0 ≤ 1 - C.contraction.c :=
      sub_nonneg.mpr C.contraction.c_lt_one.le
    have hres_le : C.residual ≤ (1 - C.contraction.c) * radius' :=
      le_trans C.residual_le_margin
        (mul_le_mul_of_nonneg_left hradius hmargin_nonneg)
    calc
      C.residual + C.contraction.c * radius' ≤
          (1 - C.contraction.c) * radius' +
            C.contraction.c * radius' := by
        exact add_le_add_left hres_le (C.contraction.c * radius')
      _ = radius' := by ring

end FinitePlusTailClosedBallContractionCertificate
end Exact3D
end StatMech
