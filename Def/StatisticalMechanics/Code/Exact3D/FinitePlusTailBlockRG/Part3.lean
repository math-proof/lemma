/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


noncomputable def with_larger_constants
    (P : FinitePlusTailBlockRGPackage n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' c' : ℝ}
    (hff : P.blockBounds.finiteToFinite ≤ finiteToFinite')
    (htf : P.blockBounds.tailToFinite ≤ tailToFinite')
    (hft : P.blockBounds.finiteToTail ≤ finiteToTail')
    (htt : P.blockBounds.tailToTail ≤ tailToTail')
    (hc_nonneg : 0 ≤ c') (hc_lt_one : c' < 1)
    (hfinite_column_sum_le : finiteToFinite' + finiteToTail' ≤ c')
    (htail_column_sum_le : tailToFinite' + tailToTail' ≤ c')
    (hdominated : c' ≤ |P.thermal|) :
    FinitePlusTailBlockRGPackage n α where
  blockBounds :=
    P.blockBounds.with_larger_constants hff htf hft htt
  c := c'
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := htail_column_sum_le
  origin_fixed := by
    simpa [FinitePlusTailBlockBounds.with_larger_constants,
      FinitePlusTailBlockBounds.map] using P.origin_fixed
  thermal := P.thermal
  thermal_gt_one := P.thermal_gt_one
  stable_dominated := hdominated

end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
