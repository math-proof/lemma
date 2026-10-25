/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailRG
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockRG.Part3


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockRGPackage

variable {n : ℕ} {α : Type}


@[simp] theorem with_larger_constants_c
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
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).c = c' :=
  rfl

@[simp] theorem with_larger_constants_blockBounds
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
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).blockBounds =
        P.blockBounds.with_larger_constants hff htf hft htt :=
  rfl

@[simp] theorem with_larger_constants_thermal
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
    (P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).thermal =
        P.thermal :=
  rfl

@[simp] theorem with_larger_constants_stableCertificate_map
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
    ((P.with_larger_constants hff htf hft htt hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le hdominated).stableCertificate).map =
      P.stableCertificate.map := by
  simp [stableCertificate]


end FinitePlusTailBlockRGPackage
end Exact3D
end StatMech
