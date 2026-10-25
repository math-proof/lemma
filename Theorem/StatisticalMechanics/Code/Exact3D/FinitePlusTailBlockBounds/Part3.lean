/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part3


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


@[simp] theorem toLipschitzCertificate_map
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).map = B.map :=
  rfl

@[simp] theorem toLipschitzCertificate_c
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).c = c :=
  rfl


theorem mixed_lipschitz
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (x y : FinitePlusTailState n α) :
    (B.map x).dist (B.map y) ≤ c * x.dist y := by
  simpa using
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).mixed_lipschitz x y


theorem exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    ∃! p : FinitePlusTailState n α, B.map p = p := by
  simpa using
    (B.toLipschitzCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le).exists_unique_fixedPoint


end FinitePlusTailBlockBounds
end Exact3D
end StatMech
