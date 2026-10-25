/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


noncomputable def with_larger_c
    (P : FinitePlusTailBlockRGPackage n α)
    {c' : ℝ} (hc : P.c ≤ c') (hc_lt_one : c' < 1)
    (hdominated : c' ≤ |P.thermal|) :
    FinitePlusTailBlockRGPackage n α where
  blockBounds := P.blockBounds
  c := c'
  c_nonneg := le_trans P.c_nonneg hc
  c_lt_one := hc_lt_one
  finite_column_sum_le := le_trans P.finite_column_sum_le hc
  tail_column_sum_le := le_trans P.tail_column_sum_le hc
  origin_fixed := P.origin_fixed
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one
  stable_dominated := hdominated

end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
