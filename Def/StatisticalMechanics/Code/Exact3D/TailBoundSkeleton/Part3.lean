/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Structure.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace ContributionSplit

def Additive (S : ContributionSplit α) : Prop :=
  ∀ a, S.totalContribution a = S.finiteContribution a + S.tailContribution a


def TailUpperBound (S : ContributionSplit α) (bound : ℝ) : Prop :=
  ∀ a, S.tailContribution a ≤ bound


def TailEnvelopeOn (S : ContributionSplit α) (s : Finset α)
    (envelope : α → ℝ) : Prop :=
  ∀ a, a ∈ s → S.tailContribution a ≤ envelope a


def TotalUpperBound (S : ContributionSplit α) (bound : ℝ) : Prop :=
  ∀ a, S.totalContribution a ≤ bound


end ContributionSplit
end Exact3D
end StatMech
