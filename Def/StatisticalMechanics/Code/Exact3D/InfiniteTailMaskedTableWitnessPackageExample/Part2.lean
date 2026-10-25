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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackageExample

noncomputable def geometricMaskedTableWitnessPackage :
    InfiniteTailMaskedTableWitnessPackage (Case := Unit) (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) where
  nStable := 1
  scale := FiniteWitnessPackageExample.exampleScale
  thermal := 3
  thermal_gt_one := by norm_num
  stable := FiniteWitnessPackageExample.stableZeroWitness
  S := geometricSplit
  finitePrefix := {0}
  table := zeroTable
  classify := zeroClassifier
  finiteBound := 0
  prefixTailBound := 1
  tailBound := 1
  tailEnvelope := InfiniteTailSummabilityExample.geometricHalfTailWeight
  total_nonneg := geometricSplit_total_nonneg
  additive := geometricSplit_additive
  finiteTable := zeroFiniteTableUpperBound
  tailEnvelopeOnPrefix := geometricTailEnvelopeOnPrefix
  prefixTailEnvelopeSum_le := geometricPrefixTailEnvelopeSum_le_one
  finite_zero_off_prefix := geometricSplit_finite_zero_off_prefix
  tailEnvelope_nonneg_off_prefix := by
    intro n _
    exact InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg n
  tail_le_tailEnvelope_off_prefix := by
    intro _ _
    exact le_rfl
  summable_masked_tailEnvelope := by
    refine
      InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_summable.congr
        ?_
    intro n
    simp [InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight]
  masked_tailEnvelope_tsum_le := by
    convert
      InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_tsum_le_one
      using 1


end InfiniteTailMaskedTableWitnessPackageExample
end Exact3D
end StatMech
