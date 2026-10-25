/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone


namespace StatMech

namespace Exact3D

structure FinitePlusTailHyperbolicSplitting (n : ℕ) (α : Type*) where
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable : FinitePlusTailLipschitzCertificate n α
  stable_origin :
    stable.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
      FinitePlusTailState.origin
  stable_dominated : stable.c ≤ |thermal|

end Exact3D
end StatMech
