import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
open StatMech StatMech.Exact3D StatMech.Exact3D.ContributionSplit


/--
[finite_le_of_tableUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean)
-/
@[path]
private lemma finite_le_of_tableUpperBound_eq
  [DecidableEq Case]
  {T : RatInterval.CaseTable Case}
  {classify : α → Case}
  {value : α → ℝ}
  {bound : ℝ}
  {a : α}
-- given
  (h : FiniteTableUpperBound T classify value bound) :
-- imply
  value a ≤ bound := by
-- proof
  apply StatMech.Exact3D.finite_le_of_tableUpperBound h a

/--
[totalUpperBound_of_finiteTableUpperBound_and_tailUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean)
-/
@[path]
private lemma totalUpperBound_of_finiteTableUpperBound_and_tailUpperBound_eq
  [DecidableEq Case]
  {S : ContributionSplit α}
  {T : RatInterval.CaseTable Case}
  {classify : α → Case}
  {finiteBound tailBound : ℝ}
-- given
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail : S.TailUpperBound tailBound) :
-- imply
  S.TotalUpperBound (finiteBound + tailBound) := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.totalUpperBound_of_finiteTableUpperBound_and_tailUpperBound S hadd hfinite htail

/--
[tail_sum_le_of_envelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean)
-/
@[path]
private lemma tail_sum_le_of_envelopeOn_eq
  {S : ContributionSplit α}
  {s : Finset α}
  {envelope : α → ℝ}
-- given
  (henv : S.TailEnvelopeOn s envelope) :
-- imply
  (∑ a ∈ s, S.tailContribution a) ≤ ∑ a ∈ s, envelope a := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.tail_sum_le_of_envelopeOn S s envelope henv

/--
[total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailBoundSkeleton.lean)
-/
@[path]
private lemma total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn_eq
  [DecidableEq Case]
  {S : ContributionSplit α}
  {s : Finset α}
  {T : RatInterval.CaseTable Case}
  {classify : α → Case}
  {finiteBound tailBound : ℝ}
  {tailEnvelope : α → ℝ}
-- given
  (hadd : S.Additive)
  (hfinite : FiniteTableUpperBound T classify S.finiteContribution finiteBound)
  (htail : S.TailEnvelopeOn s tailEnvelope)
  (htailSum : (∑ a ∈ s, tailEnvelope a) ≤ tailBound) :
-- imply
  (∑ a ∈ s, S.totalContribution a) ≤ (s.card : ℝ) * finiteBound + tailBound := by
-- proof
  apply StatMech.Exact3D.ContributionSplit.total_sum_le_of_finiteTableUpperBound_and_tailEnvelopeOn S s tailEnvelope hadd hfinite htail htailSum


-- created on 2026-10-23
