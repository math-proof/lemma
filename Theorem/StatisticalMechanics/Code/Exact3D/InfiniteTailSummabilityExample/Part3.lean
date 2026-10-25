/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

theorem maskedGeometricHalfTailWeight_nonneg (n : ℕ) :
    0 ≤ maskedGeometricHalfTailWeight n := by
  unfold maskedGeometricHalfTailWeight
  by_cases hn : n ∈ ({0} : Finset ℕ)
  · simp [hn]
  · simpa [hn] using geometricHalfTailWeight_nonneg n


theorem maskedGeometricHalfTailWeight_le_geometricHalfTailWeight (n : ℕ) :
    maskedGeometricHalfTailWeight n ≤ geometricHalfTailWeight n := by
  unfold maskedGeometricHalfTailWeight
  by_cases hn : n ∈ ({0} : Finset ℕ)
  · simpa [hn] using geometricHalfTailWeight_nonneg n
  · simp [hn]


theorem maskedGeometricHalfTailWeight_summable :
    Summable maskedGeometricHalfTailWeight :=
  Summable.of_nonneg_of_le maskedGeometricHalfTailWeight_nonneg
    maskedGeometricHalfTailWeight_le_geometricHalfTailWeight
    geometricHalfTailWeight_summable


theorem maskedGeometricHalfTailWeight_tsum_le_one :
    (∑' n : ℕ, maskedGeometricHalfTailWeight n) ≤ 1 :=
  le_trans
    (Summable.tsum_le_tsum
      maskedGeometricHalfTailWeight_le_geometricHalfTailWeight
      maskedGeometricHalfTailWeight_summable
      geometricHalfTailWeight_summable)
    (by rw [geometricHalfTailWeight_tsum_eq_one])


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
