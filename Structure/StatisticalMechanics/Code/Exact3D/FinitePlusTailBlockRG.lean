/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG


namespace StatMech

namespace Exact3D

structure FinitePlusTailBlockRGPackage (n : ℕ) (α : Type) where
  blockBounds : FinitePlusTailBlockBounds n α
  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  finite_column_sum_le : blockBounds.finiteToFinite + blockBounds.finiteToTail ≤ c
  tail_column_sum_le : blockBounds.tailToFinite + blockBounds.tailToTail ≤ c
  origin_fixed :
    blockBounds.map (FinitePlusTailState.origin : FinitePlusTailState n α) =
      FinitePlusTailState.origin
  thermal : ℝ
  thermal_gt_one : 1 < thermal
  stable_dominated : c ≤ |thermal|

end Exact3D
end StatMech
