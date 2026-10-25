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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

noncomputable def geometricContributionSplitTailEnvelopeWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofContributionSplitTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    geometricContributionSplit
    (∅ : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro n
      simp [geometricContributionSplit])
    (by
      intro n _
      simp [geometricContributionSplit])
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
    (by
      intro _ _
      rfl)
    InfiniteTailSummabilityExample.geometricHalfTailWeight_summable
    (by
      rw [InfiniteTailSummabilityExample.geometricHalfTailWeight_tsum_eq_one])


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
