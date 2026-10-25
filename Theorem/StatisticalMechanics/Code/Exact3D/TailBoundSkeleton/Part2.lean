/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part39
import Def.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace ContributionSplit

theorem totalUpperBound_of_finiteTableUpperBound_and_tailUpperBound
    {Case α : Type*} [DecidableEq Case]
    (S : ContributionSplit α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailBound : ℝ}
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailUpperBound tailBound) :
    S.TotalUpperBound (finiteBound + tailBound) := by
  intro a
  calc
    S.totalContribution a =
        S.finiteContribution a + S.tailContribution a := hadd a
    _ ≤ finiteBound + tailBound :=
        add_le_add (finite_le_of_tableUpperBound hfinite a) (htail a)


theorem tail_sum_le_of_envelopeOn
    (S : ContributionSplit α) (s : Finset α) (envelope : α → ℝ)
    (henv : S.TailEnvelopeOn s envelope) :
    (∑ a ∈ s, S.tailContribution a) ≤ ∑ a ∈ s, envelope a := by
  exact Finset.sum_le_sum fun a ha => henv a ha


theorem total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn
    {Case α : Type*} [DecidableEq Case]
    (S : ContributionSplit α) (s : Finset α)
    {T : RatInterval.CaseTable Case} {classify : α → Case}
    {finiteBound tailBound : ℝ} (tailEnvelope : α → ℝ)
    (hadd : S.Additive)
    (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
    (htail : S.TailEnvelopeOn s tailEnvelope)
    (htailSum : (∑ a ∈ s, tailEnvelope a) ≤ tailBound) :
    (∑ a ∈ s, S.totalContribution a) ≤
      (s.card : ℝ) * finiteBound + tailBound := by
  calc
    (∑ a ∈ s, S.totalContribution a) =
        ∑ a ∈ s, (S.finiteContribution a + S.tailContribution a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hadd a
    _ = (∑ a ∈ s, S.finiteContribution a) +
        ∑ a ∈ s, S.tailContribution a := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ _a ∈ s, finiteBound) + ∑ a ∈ s, tailEnvelope a := by
      exact add_le_add
        (Finset.sum_le_sum fun a _ => finite_le_of_tableUpperBound hfinite a)
        (tail_sum_le_of_envelopeOn S s tailEnvelope htail)
    _ ≤ (s.card : ℝ) * finiteBound + tailBound := by
      apply add_le_add
      · simp [Finset.sum_const, nsmul_eq_mul]
      · exact htailSum

end ContributionSplit
end Exact3D
end StatMech
