/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

noncomputable def geometricContributionSplit : ContributionSplit ℕ where
  finiteContribution := fun _ => 0
  tailContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight
  totalContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight


noncomputable def geometricContributionSplitMaskedTailEnvelopeWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofContributionSplitMaskedTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    geometricContributionSplit
    ({0} : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro n
      simp [geometricContributionSplit])
    (by
      intro n _
      simp [geometricContributionSplit])
    (by
      intro n _
      exact InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg n)
    (by
      intro _ _
      exact le_rfl)
    (by
      refine
        InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_summable.congr
          ?_
      intro n
      simp [InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight])
    (by
      convert
        InfiniteTailSummabilityExample.maskedGeometricHalfTailWeight_tsum_le_one
        using 1)


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
