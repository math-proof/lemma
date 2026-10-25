/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part3


namespace StatMech

namespace Exact3D

structure FinitePlusTailConeCertificate (n : ℕ) (α : Type*) where
  contraction : FinitePlusTailLipschitzCertificate n α
  thermal : FinitePlusTailState n α → ℝ
  stableSize : FinitePlusTailState n α → ℝ
  thermalMultiplier : ℝ
  stableStepConstant : ℝ
  stableSize_nonneg : ∀ x, 0 ≤ stableSize x
  stableStepConstant_nonneg : 0 ≤ stableStepConstant
  thermal_step :
    ∀ x, thermal (contraction.map x) = thermalMultiplier * thermal x
  stable_step_bound :
    ∀ x,
      stableSize (contraction.map x) ≤
        stableStepConstant * stableSize x
  stable_dominated : stableStepConstant ≤ |thermalMultiplier|

end Exact3D
end StatMech
