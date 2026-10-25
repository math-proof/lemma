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
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part11
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


@[simp] theorem ofFiniteMap_map_ofFinite
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite : FiniteContraction.LipschitzWithConstant finiteMap c)
    (x : Fin n → ℝ) :
    ((ofFiniteMap (α := α) finiteMap hc_nonneg hc_lt_one hfinite).map
      (FinitePlusTailState.ofFinite x)) =
        FinitePlusTailState.ofFinite (α := α) (finiteMap x) :=
  rfl


theorem l1Dist_scaleFinite (c : ℝ) (x y : Fin n → ℝ) :
    FiniteContraction.l1Dist (fun i => c * x i) (fun i => c * y i) =
      |c| * FiniteContraction.l1Dist x y := by
  unfold FiniteContraction.l1Dist RatInterval.supNormVec
  calc
    (∑ i, |c * x i - c * y i|) =
        ∑ i, |c| * |x i - y i| := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have h : c * x i - c * y i = c * (x i - y i) := by ring
      rw [h, abs_mul]
    _ = |c| * ∑ i, |x i - y i| := by
      rw [Finset.mul_sum]


end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
