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
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailWitnessPackageExample

noncomputable def geometricTailWitnessPackage :
    InfiniteTailWitnessPackage (α := ℕ)
      (ToyCriticalModel FiniteWitnessPackageExample.exampleScale 3) where
  nStable := 1
  scale := FiniteWitnessPackageExample.exampleScale
  thermal := 3
  thermal_gt_one := by norm_num
  stable := FiniteWitnessPackageExample.stableZeroWitness
  tailCertificate :=
    InfiniteTailSummabilityExample.geometricHalfInfiniteTailCertificate


end InfiniteTailWitnessPackageExample
end Exact3D
end StatMech
