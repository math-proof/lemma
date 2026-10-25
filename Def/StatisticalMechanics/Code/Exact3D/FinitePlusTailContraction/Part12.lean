/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part14
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


noncomputable def decoupledScaling
    (finiteScale tailScale c : ℝ)
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_abs_le : |finiteScale| ≤ c)
    (htail_abs_le : |tailScale| ≤ c) :
    FinitePlusTailLipschitzCertificate n α :=
  ofDecoupled
    (fun x i => finiteScale * x i)
    (SummableTail.scale tailScale)
    (finiteConstant := |finiteScale|)
    (tailConstant := |tailScale|)
    (c := c)
    (abs_nonneg finiteScale)
    (abs_nonneg tailScale)
    hc_nonneg
    hc_lt_one
    hfinite_abs_le
    htail_abs_le
    (by
      intro x y
      rw [l1Dist_scaleFinite])
    (by
      intro u v
      rw [SummableTail.dist_scale])


noncomputable def ofColumnSumFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail c : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    (hfinite_column_sum_le : (hI.c : ℝ) + finiteToTail ≤ c)
    (htail_column_sum_le : tailToTail ≤ c)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailLipschitzCertificate n α where
  map := fun x =>
    { finite := fun i => RatInterval.matVec A x.finite i
      tail := tailMap x }
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  c := c
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_matVec_of_columnSumContraction hI hA
        x.finite y.finite
  tail_bound := htail_bound
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := by
    simpa using htail_column_sum_le


noncomputable def ofColumnSumAffineFiniteBlock
    {I : RatInterval.IntervalMatrix n n}
    (hI : RatInterval.ColumnSumContraction I)
    {A : Fin n → Fin n → ℝ} (hA : RatInterval.MatrixMem A I)
    (offset : Fin n → ℝ)
    (tailMap : FinitePlusTailState n α → SummableTail α)
    {finiteToTail tailToTail c : ℝ}
    (hfiniteToTail_nonneg : 0 ≤ finiteToTail)
    (htailToTail_nonneg : 0 ≤ tailToTail)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    (hfinite_column_sum_le : (hI.c : ℝ) + finiteToTail ≤ c)
    (htail_column_sum_le : tailToTail ≤ c)
    (htail_bound :
      ∀ x y,
        (tailMap x).dist (tailMap y) ≤
          finiteToTail * x.finiteDist y + tailToTail * x.tailDist y) :
    FinitePlusTailLipschitzCertificate n α where
  map := fun x =>
    { finite := fun i => RatInterval.affineMap A offset x.finite i
      tail := tailMap x }
  finiteToFinite := (hI.c : ℝ)
  tailToFinite := 0
  finiteToTail := finiteToTail
  tailToTail := tailToTail
  c := c
  finiteToFinite_nonneg := by
    exact_mod_cast hI.c_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := hfiniteToTail_nonneg
  tailToTail_nonneg := htailToTail_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      FiniteContraction.lipschitz_affineMap_of_columnSumContraction hI hA offset
        x.finite y.finite
  tail_bound := htail_bound
  finite_column_sum_le := hfinite_column_sum_le
  tail_column_sum_le := by
    simpa using htail_column_sum_le

end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
