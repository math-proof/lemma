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
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part13
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailLipschitzCertificate

variable {n : ℕ} {α : Type*}


noncomputable def ofDecoupled
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ)
    (tailMap : SummableTail α → SummableTail α)
    {finiteConstant tailConstant c : ℝ}
    (hfiniteConstant_nonneg : 0 ≤ finiteConstant)
    (htailConstant_nonneg : 0 ≤ tailConstant)
    (hc_nonneg : 0 ≤ c)
    (hc_lt_one : c < 1)
    (hfinite_le_c : finiteConstant ≤ c)
    (htail_le_c : tailConstant ≤ c)
    (hfinite :
      ∀ x y,
        FiniteContraction.l1Dist (finiteMap x) (finiteMap y) ≤
          finiteConstant * FiniteContraction.l1Dist x y)
    (htail :
      ∀ u v, (tailMap u).dist (tailMap v) ≤ tailConstant * u.dist v) :
    FinitePlusTailLipschitzCertificate n α where
  map := fun x => { finite := finiteMap x.finite, tail := tailMap x.tail }
  finiteToFinite := finiteConstant
  tailToFinite := 0
  finiteToTail := 0
  tailToTail := tailConstant
  c := c
  finiteToFinite_nonneg := hfiniteConstant_nonneg
  tailToFinite_nonneg := by norm_num
  finiteToTail_nonneg := by norm_num
  tailToTail_nonneg := htailConstant_nonneg
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  finite_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      hfinite x.finite y.finite
  tail_bound := by
    intro x y
    simpa [FinitePlusTailState.finiteDist, FinitePlusTailState.tailDist] using
      htail x.tail y.tail
  finite_column_sum_le := by
    simpa using hfinite_le_c
  tail_column_sum_le := by
    simpa using htail_le_c


noncomputable def ofFiniteMap
    (finiteMap : (Fin n → ℝ) → Fin n → ℝ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite : FiniteContraction.LipschitzWithConstant finiteMap c) :
    FinitePlusTailLipschitzCertificate n α :=
  ofDecoupled finiteMap (fun _ => (0 : SummableTail α))
    (finiteConstant := c) (tailConstant := 0) (c := c)
    hc_nonneg (by norm_num) hc_nonneg hc_lt_one
    (le_refl c) hc_nonneg
    hfinite
    (by
      intro u v
      simp [SummableTail.dist_self])

end FinitePlusTailLipschitzCertificate
end Exact3D
end StatMech
