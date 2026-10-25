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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

noncomputable def geometricTailWitnessPackageFromEnvelope :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) :=
  InfiniteTailWitnessPackage.ofTailEnvelope
    (α := ℕ) (thermal := 3)
    (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3)
    FiniteWitnessPackageExample.exampleScale
    (by norm_num)
    FiniteWitnessPackageExample.stableZeroWitness
    (∅ : Finset ℕ)
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight
    InfiniteTailSummabilityExample.geometricHalfTailWeight_nonneg
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
