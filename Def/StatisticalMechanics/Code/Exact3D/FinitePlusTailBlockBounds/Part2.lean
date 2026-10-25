/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def with_larger_constants
    (B : FinitePlusTailBlockBounds n α)
    {finiteToFinite' tailToFinite' finiteToTail' tailToTail' : ℝ}
    (hff : B.finiteToFinite ≤ finiteToFinite')
    (htf : B.tailToFinite ≤ tailToFinite')
    (hft : B.finiteToTail ≤ finiteToTail')
    (htt : B.tailToTail ≤ tailToTail') :
    FinitePlusTailBlockBounds n α where
  finiteMap := B.finiteMap
  tailMap := B.tailMap
  finiteToFinite := finiteToFinite'
  tailToFinite := tailToFinite'
  finiteToTail := finiteToTail'
  tailToTail := tailToTail'
  finiteToFinite_nonneg := le_trans B.finiteToFinite_nonneg hff
  tailToFinite_nonneg := le_trans B.tailToFinite_nonneg htf
  finiteToTail_nonneg := le_trans B.finiteToTail_nonneg hft
  tailToTail_nonneg := le_trans B.tailToTail_nonneg htt
  finite_bound := by
    intro x y
    have hfinite_nonneg : 0 ≤ x.finiteDist y :=
      FinitePlusTailState.finiteDist_nonneg x y
    have htail_nonneg : 0 ≤ x.tailDist y :=
      FinitePlusTailState.tailDist_nonneg x y
    calc
      FiniteContraction.l1Dist (B.finiteMap x) (B.finiteMap y) ≤
          B.finiteToFinite * x.finiteDist y +
            B.tailToFinite * x.tailDist y :=
        B.finite_bound x y
      _ ≤
          finiteToFinite' * x.finiteDist y +
            tailToFinite' * x.tailDist y := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hff hfinite_nonneg)
          (mul_le_mul_of_nonneg_right htf htail_nonneg)
  tail_bound := by
    intro x y
    have hfinite_nonneg : 0 ≤ x.finiteDist y :=
      FinitePlusTailState.finiteDist_nonneg x y
    have htail_nonneg : 0 ≤ x.tailDist y :=
      FinitePlusTailState.tailDist_nonneg x y
    calc
      (B.tailMap x).dist (B.tailMap y) ≤
          B.finiteToTail * x.finiteDist y +
            B.tailToTail * x.tailDist y :=
        B.tail_bound x y
      _ ≤
          finiteToTail' * x.finiteDist y +
            tailToTail' * x.tailDist y := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hft hfinite_nonneg)
          (mul_le_mul_of_nonneg_right htt htail_nonneg)

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
