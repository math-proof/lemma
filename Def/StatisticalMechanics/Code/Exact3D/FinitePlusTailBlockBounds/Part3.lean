/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part2


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


noncomputable def ofDecoupled
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ)
    (tailMap : SummableTail α → SummableTail α)
    {finiteConstant tailConstant : ℝ}
    (hfiniteConstant_nonneg : 0 ≤ finiteConstant)
    (htailConstant_nonneg : 0 ≤ tailConstant)
    (hfinite :
      ∀ x y,
        FiniteContraction.l1Dist (finiteMap x) (finiteMap y) ≤
          finiteConstant * FiniteContraction.l1Dist x y)
    (htail :
      ∀ u v, (tailMap u).dist (tailMap v) ≤ tailConstant * u.dist v) :
    FinitePlusTailBlockBounds n α where
  finiteMap := fun x => finiteMap x.finite
  tailMap := fun x => tailMap x.tail
  finiteToFinite := finiteConstant
  tailToFinite := 0
  finiteToTail := 0
  tailToTail := tailConstant
  finiteToFinite_nonneg := hfiniteConstant_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := by norm_num
  tailToTail_nonneg := htailConstant_nonneg
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      hfinite x.finite y.finite
  tail_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      htail x.tail y.tail


noncomputable def decoupledScaling
    (finiteScale tailScale : ℝ) :
    FinitePlusTailBlockBounds n α :=
  ofDecoupled
    (fun x i => finiteScale * x i)
    (SummableTail.scale tailScale)
    (finiteConstant := |finiteScale|)
    (tailConstant := |tailScale|)
    (abs_nonneg finiteScale)
    (abs_nonneg tailScale)
    (by
      intro x y
      rw [FinitePlusTailLipschitzCertificate.l1Dist_scaleFinite])
    (by
      intro u v
      rw [SummableTail.dist_scale])


noncomputable def ofColumnSumFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailBlockBounds n α where
  finiteMap := fun x i => RatInterval.matVec A x.finite i
  tailMap := tailMap
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_matVec_of_columnSumContraction hI hA
        x.finite y.finite
  tail_bound := htail_bound


noncomputable def ofColumnSumAffineFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (offset : Fin n → ℝ)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailBlockBounds n α where
  finiteMap := fun x i => RatInterval.affineMap A offset x.finite i
  tailMap := tailMap
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_affineMap_of_columnSumContraction hI hA offset
        x.finite y.finite
  tail_bound := htail_bound


noncomputable def toLipschitzCertificate
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c) :
    FinitePlusTailLipschitzCertificate n α where
  map := B.map
  finiteToFinite := B.finiteToFinite
  tailToFinite := B.tailToFinite
  finiteToTail := B.finiteToTail
  tailToTail := B.tailToTail
  c := c
  finiteToFinite_nonneg := B.finiteToFinite_nonneg
  tailToFinite_nonneg := B.tailToFinite_nonneg
  finiteToTail_nonneg := B.finiteToTail_nonneg
  tailToTail_nonneg := B.tailToTail_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := B.map_finite_bound
  tail_bound := B.map_tail_bound
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := htail_column_sum_le

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
