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
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailMaskedTableWitnessPackageExample

noncomputable def geometricSplit : ContributionSplit ℕ where
  finiteContribution := fun _ => 0
  tailContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight
  totalContribution := InfiniteTailSummabilityExample.geometricHalfTailWeight


def zeroTable : RatInterval.CaseTable Unit where
  cases := Finset.univ
  interval := fun _ => RatInterval.point 0


def zeroClassifier (_ : ℕ) : Unit := ()


end InfiniteTailMaskedTableWitnessPackageExample
end Exact3D
end StatMech
