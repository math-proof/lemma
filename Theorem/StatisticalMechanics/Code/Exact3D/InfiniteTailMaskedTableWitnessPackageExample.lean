/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackageExample

theorem geometricSplit_additive : geometricSplit.Additive := by
  intro n
  simp [geometricSplit]


theorem geometricSplit_total_nonneg :
    ∀ n : ℕ, 0 ≤ geometricSplit.totalContribution n :=
  InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg


theorem zeroFiniteTableUpperBound :
    FiniteTableUpperBound zeroTable zeroClassifier
      geometricSplit.finiteContribution 0 where
  covers := by
    intro n
    simp [zeroTable, zeroClassifier]
  sound := by
    intro n
    norm_num [RatInterval.CaseTable.Sound, zeroTable, zeroClassifier,
      geometricSplit, RatInterval.point, RatInterval.MemR]
  intervalUpper_le := by
    intro c _
    cases c
    norm_num [zeroTable, RatInterval.point]


theorem geometricTailEnvelopeOnPrefix :
    geometricSplit.TailEnvelopeOn ({0} : Finset ℕ)
      InfiniteTailSummabilityExample.geometricHalfTailWeight := by
  intro n _
  exact le_rfl


theorem geometricPrefixTailEnvelopeSum_le_one :
    (∑ n ∈ ({0} : Finset ℕ),
      InfiniteTailSummabilityExample.geometricHalfTailWeight n) ≤ 1 := by
  norm_num [InfiniteTailSummabilityExample.geometricHalfTailWeight]


theorem geometricSplit_finite_zero_off_prefix :
    ∀ n : ℕ, n ∉ ({0} : Finset ℕ) →
      geometricSplit.finiteContribution n = 0 := by
  intro n _
  rfl


end InfiniteTailMaskedTableWitnessPackageExample
end Exact3D
end StatMech
