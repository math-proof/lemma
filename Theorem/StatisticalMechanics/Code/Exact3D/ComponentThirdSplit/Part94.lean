/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part99
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleStrictTotal_of_residualCaseNormalizedLabelRowsCanonicalRaw
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label) := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hraw β hβpos hβc] with
    n hnR hnRaw
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  let row : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ i : ι Ωnz v x,
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (label Ωnz v x) i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hraw' :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) < R := by
    simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail, row] using
      hnRaw H hH Ω v hv
  have hshare :=
    liveSingletonOptionStrictTotalShare_lt_one_of_rawNumerator_lt
      liveOptions R remaining tail row hRpos hraw'
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows,
    liveSingletonOptionNormalizedRemainingShare, liveSingletonOptionNormalizedTailShare,
    Finset.sum_div, Ωnz, cap, D, paid, R, liveOptions, remaining, tail, row] using
    hshare

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleRemainderPositive_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hstrict⟩
  let singletonBudgetSum : ℝ := ∑ x ∈ liveOptions, singletonBudget x
  have hremainingNonneg : 0 ≤ remaining := by
    simpa [remaining] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have htailNonneg : 0 ≤ tail := by
    simpa [tail] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hbudgetNonneg : ∀ x ∈ liveOptions, 0 ≤ singletonBudget x := by
    intro x hx
    have hsourceNonneg :
        0 ≤
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v true true true ∪
          ({x} : Finset (Option (FK.boxVerts 3 n))))
    exact le_trans hsourceNonneg (hpoint x hx)
  have hbudgetSumNonneg : 0 ≤ singletonBudgetSum := by
    dsimp [singletonBudgetSum]
    exact Finset.sum_nonneg fun x hx => hbudgetNonneg x hx
  have hlhsNonneg : 0 ≤ remaining + (singletonBudgetSum + tail) :=
    add_nonneg hremainingNonneg (add_nonneg hbudgetSumNonneg htailNonneg)
  have hstrict' : remaining + (singletonBudgetSum + tail) < R := by
    simpa [remaining, singletonBudgetSum, tail, R, liveOptions, Ωnz, cap, D,
      paid] using hstrict
  exact lt_of_le_of_lt hlhsNonneg hstrict'

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  let row : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ E ∈
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ωnz true true true
        ({x} : Finset (Option (FK.boxVerts 3 n))),
      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hstrict⟩
  have hrow_le_budget : ∀ x ∈ liveOptions, row x ≤ singletonBudget x := by
    intro x hx
    have hsource :
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
          singletonBudget x := by
      simpa [Ωnz] using hpoint x hx
    have hrow_eq :
        row x =
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
      simpa [row] using
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
          β H n Ωnz v true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).symm
    exact hrow_eq.trans_le hsource
  have hsum_le :
      (∑ x ∈ liveOptions, row x) ≤
        ∑ x ∈ liveOptions, singletonBudget x :=
    Finset.sum_le_sum fun x hx => hrow_le_budget x hx
  have hstrict' :
      remaining + ((∑ x ∈ liveOptions, singletonBudget x) + tail) < R := by
    simpa [remaining, tail, R, liveOptions, Ωnz, cap, D, paid] using
      hstrict
  have hmono :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) ≤
        remaining + ((∑ x ∈ liveOptions, singletonBudget x) + tail) :=
    add_le_add le_rfl (add_le_add hsum_le le_rfl)
  exact lt_of_le_of_lt hmono hstrict'

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
      label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  let row : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ i : ι Ωnz v x,
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (label Ωnz v x) i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hstrict⟩
  have hrow_le_budget : ∀ x ∈ liveOptions, row x ≤ singletonBudget x := by
    intro x hx
    have hsource :
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
          singletonBudget x := by
      simpa [Ωnz] using hpoint x hx
    have hrow_eq :
        row x =
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
      rw [
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
          β H n Ωnz v true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (label Ωnz v x)]
      simp [row,
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet]
    exact hrow_eq.trans_le hsource
  have hsum_le :
      (∑ x ∈ liveOptions, row x) ≤
        ∑ x ∈ liveOptions, singletonBudget x :=
    Finset.sum_le_sum fun x hx => hrow_le_budget x hx
  have hstrict' :
      remaining + ((∑ x ∈ liveOptions, singletonBudget x) + tail) < R := by
    simpa [remaining, tail, R, liveOptions, Ωnz, cap, D, paid] using
      hstrict
  have hmono :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) ≤
        remaining + ((∑ x ∈ liveOptions, singletonBudget x) + tail) :=
    add_le_add le_rfl (add_le_add hsum_le le_rfl)
  exact lt_of_le_of_lt hmono hstrict'

set_option linter.style.longLine false in


theorem liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hraw β hβpos hβc] with n hnRaw
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  let singletonBudget : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ E ∈
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ωnz true true true
        ({x} : Finset (Option (FK.boxVerts 3 n))),
      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  refine ⟨singletonBudget, ?_, ?_⟩
  · intro x hx
    have hbudget_eq :
        singletonBudget x =
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
      simpa [singletonBudget] using
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
          β H n Ωnz v true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).symm
    exact le_of_eq hbudget_eq.symm
  · have hstrict :
        remaining + ((∑ x ∈ liveOptions, singletonBudget x) + tail) < R := by
      simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail,
        singletonBudget] using hnRaw H hH Ω v hv
    simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail,
      singletonBudget] using hstrict

set_option linter.style.longLine false in


theorem liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_iff_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical :=
  ⟨liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree,
    liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal⟩

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleComponents
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFreeAbsorption_of_componentBudgetSchedule
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorption_of_components
          hremaining htail hsingleton hpayment)))

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleComponents
    hremaining htail
    (liveSingletonOptionComponentBudgetScheduleSingleton_of_namedResidualCaseShareBudget
      hsingletonResidual)
    hpayment

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_pointwiseRowsCanonicalRawStrictTotal
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
      label :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    (liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal
      hraw)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleComponents
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
      label :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_pointwiseRowsCanonicalRawStrictTotal
    (label := label)
    (liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleComponents
      hremaining htail hsingleton hpayment)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
      label :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_pointwiseRowsCanonicalRawStrictTotal
    (label := label)
    (liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton
      hremaining htail hpayment hsingletonResidual)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_labelRowsCanonicalRawStrictTotal
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hraw β hβpos hβc] with n hnRaw
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  let pointwiseRow : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ E ∈
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ωnz true true true
        ({x} : Finset (Option (FK.boxVerts 3 n))),
      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  let labelRow : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ i : ι Ωnz v x,
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (label Ωnz v x) i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  have hrow_eq : ∀ x, pointwiseRow x = labelRow x := by
    intro x
    have hpoint :
        pointwiseRow x =
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
      simpa [pointwiseRow] using
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
          β H n Ωnz v true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).symm
    have hlabel :
        labelRow x =
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
      rw [
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
          β H n Ωnz v true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (label Ωnz v x)]
      simp [labelRow,
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet]
    exact hpoint.trans hlabel.symm
  have hsum_eq :
      (∑ x ∈ liveOptions, pointwiseRow x) =
        ∑ x ∈ liveOptions, labelRow x :=
    Finset.sum_congr rfl fun x _hx => hrow_eq x
  have hlabel_raw :
      remaining + ((∑ x ∈ liveOptions, labelRow x) + tail) < R := by
    simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail, labelRow] using
      hnRaw H hH Ω v hv
  have hpointwise_raw :
      remaining + ((∑ x ∈ liveOptions, pointwiseRow x) + tail) < R := by
    rw [hsum_eq]
    exact hlabel_raw
  simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail,
    pointwiseRow] using hpointwise_raw

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_iff_pointwiseRowsCanonicalRawStrictTotal
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x} :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical :=
  ⟨liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_labelRowsCanonicalRawStrictTotal,
    liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_pointwiseRowsCanonicalRawStrictTotal⟩

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingleton_of_residualCaseNormalizedLabelRows
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ i : ι Ωnz v x,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) i,
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
      schedule := by
  refine
    liveSingletonOptionShareScheduleSingleton_of_residualCaseLabelShareBudget
      (schedule := schedule) (label := label) ?_
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hpayment β hβpos hβc] with
    n hnR hnPayment
  intro H hH Ω v hv
  dsimp only
  intro x hx
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  refine
    ⟨R,
      fun i =>
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ωnz true true true
            ({x} : Finset (Option (FK.boxVerts 3 n)))
            (label Ωnz v x) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / R,
      ?_, ?_⟩
  · have hpointwise :
        SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
          v β H Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (fun E =>
            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
              β H E / R)
          R :=
      sourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare_of_denominatorPositive
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
        (le_of_lt hβpos) (le_of_lt hH) hRpos
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare_of_pointwiseShare
        (v := v) (β := β) (H := H) (Ω := Ωnz) (D := R)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
        (atomShare := fun E =>
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / R)
        hpointwise
        (label := label Ωnz v x)
  · have hshare :
        (∑ i : ι Ωnz v x,
          ∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ωnz true true true
            ({x} : Finset (Option (FK.boxVerts 3 n)))
            (label Ωnz v x) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / R) ≤
          schedule.singletonShare β H Ωnz v x := by
      simpa [Ωnz, cap, D, paid, R] using
        hnPayment H hH Ω v hv x hx
    exact mul_le_mul_of_nonneg_right hshare (le_of_lt hRpos)

set_option linter.style.longLine false in


theorem
    liveSingletonOptionShareScheduleResidualCaseSingletonPayment_of_residualCaseNormalizedPointwiseRows
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  ∃ residualShare residualDenominator : ℝ,
                    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                      v β H Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n)))
                      residualShare residualDenominator ∧
                    residualShare * residualDenominator ≤
                      schedule.singletonShare β H Ωnz v x * R := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hpayment β hβpos hβc] with
    n hnR hnPayment
  intro H hH Ω v hv
  dsimp only
  intro x hx
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  refine
    ⟨∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E /
          R,
      R, ?_, ?_⟩
  · exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_denominatorPositive
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
        (le_of_lt hβpos) (le_of_lt hH) hRpos
  · have hshare :
        (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz true true true
            ({x} : Finset (Option (FK.boxVerts 3 n))),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / R) ≤
          schedule.singletonShare β H Ωnz v x := by
      simpa [Ωnz, cap, D, paid, R] using
        hnPayment H hH Ω v hv x hx
    exact mul_le_mul_of_nonneg_right hshare (le_of_lt hRpos)

set_option linter.style.longLine false in


theorem
    liveSingletonOptionShareScheduleResidualCaseSingletonPayment_of_residualCaseNormalizedLabelRows
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ i : ι Ωnz v x,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) i,
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  ∃ residualShare residualDenominator : ℝ,
                    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                      v β H Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n)))
                      residualShare residualDenominator ∧
                    residualShare * residualDenominator ≤
                      schedule.singletonShare β H Ωnz v x * R := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hpayment β hβpos hβc] with
    n hnR hnPayment
  intro H hH Ω v hv
  dsimp only
  intro x hx
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  refine
    ⟨∑ i : ι Ωnz v x,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ωnz true true true
            ({x} : Finset (Option (FK.boxVerts 3 n)))
            (label Ωnz v x) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / R,
      R, ?_, ?_⟩
  · exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelDenominatorPositive
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
        (label := label Ωnz v x)
        (le_of_lt hβpos) (le_of_lt hH) hRpos
  · have hshare :
        (∑ i : ι Ωnz v x,
          ∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ωnz true true true
              ({x} : Finset (Option (FK.boxVerts 3 n)))
              (label Ωnz v x) i,
            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
              β H E / R) ≤
          schedule.singletonShare β H Ωnz v x := by
      simpa [Ωnz, cap, D, paid, R] using
        hnPayment H hH Ω v hv x hx
    exact mul_le_mul_of_nonneg_right hshare (le_of_lt hRpos)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingletonNonnegative_of_singletonBound
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonNonnegativePositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hsingleton β hβpos hβc] with
    n hnR hnSingleton
  intro H hH Ω v hv
  dsimp only
  intro x hx
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hsourceNonneg :
      0 ≤
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ωnz v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
      (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
      (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v true true true ∪
        ({x} : Finset (Option (FK.boxVerts 3 n))))
  have hscaledNonneg :
      0 ≤ schedule.singletonShare β H Ωnz v x * R :=
    le_trans hsourceNonneg
      (by
        simpa [Ωnz, cap, D, paid, R] using
          hnSingleton H hH Ω v hv x hx)
  have hdivNonneg :
      0 ≤ (schedule.singletonShare β H Ωnz v x * R) / R :=
    div_nonneg hscaledNonneg (le_of_lt hRpos)
  have hrewrite :
      (schedule.singletonShare β H Ωnz v x * R) / R =
        schedule.singletonShare β H Ωnz v x := by
    field_simp [hRpos.ne']
  simpa [hrewrite] using hdivNonneg

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingletonNonnegative_of_residualCaseShareBudget
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (h :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  ∃ residualShare residualDenominator : ℝ,
                    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                      v β H Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n)))
                      residualShare residualDenominator ∧
                    0 ≤ residualDenominator ∧
                      residualShare * residualDenominator ≤
                        schedule.singletonShare β H Ωnz v x * R) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonNonnegativePositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, h β hβpos hβc] with n hnR hn
  intro H hH Ω v hv
  dsimp only
  intro x hx
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  rcases hn H hH Ω v hv x hx with
    ⟨residualShare, residualDenominator, hshare, hdenomNonneg,
      hpayment⟩
  have hleftNonneg : 0 ≤ residualShare * residualDenominator :=
    mul_nonneg hshare.1 hdenomNonneg
  have hscaledNonneg :
      0 ≤ schedule.singletonShare β H Ωnz v x * R :=
    le_trans hleftNonneg hpayment
  have hdivNonneg :
      0 ≤ (schedule.singletonShare β H Ωnz v x * R) / R :=
    div_nonneg hscaledNonneg (le_of_lt hRpos)
  have hrewrite :
      (schedule.singletonShare β H Ωnz v x * R) / R =
        schedule.singletonShare β H Ωnz v x := by
    field_simp [hRpos.ne']
  simpa [hrewrite] using hdivNonneg

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_components
    {schedule : LiveSingletonOptionShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleBudgetPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards
    [hbudget β hβpos hβc, hremaining β hβpos hβc,
      htail β hβpos hβc, hsingleton β hβpos hβc] with
    n hnBudget hnRemaining hnTail hnSingleton
  intro H hH Ω v hv
  rcases hnBudget H hH Ω v hv with
    ⟨hRpos, hremainingNonneg, htailNonneg, hsingletonNonneg,
      hstrict⟩
  exact
    ⟨hRpos, hremainingNonneg, htailNonneg, hsingletonNonneg,
      hnRemaining H hH Ω v hv, hnTail H hH Ω v hv,
      hnSingleton H hH Ω v hv, hstrict⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_fine_components
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hremainingNonneg :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingNonnegativePositiveSubcritical
        schedule)
    (htailNonneg :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailNonnegativePositiveSubcritical
        schedule)
    (hsingletonNonneg :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonNonnegativePositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_components
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleBudgetPositive_of_parts
      hR hremainingNonneg htailNonneg hsingletonNonneg hstrict)
    hremaining htail hsingleton

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_derivedSignComponents
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_fine_components
    hR
    (liveSingletonOptionShareScheduleRemainingNonnegative_of_remainingBound
      hR hremaining)
    (liveSingletonOptionShareScheduleTailNonnegative_of_tailBound
      hR htail)
    (liveSingletonOptionShareScheduleSingletonNonnegative_of_singletonBound
      hR hsingleton)
    hstrict hremaining htail hsingleton

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseNormalizedPointwiseRowsDerivedSignComponents
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_derivedSignComponents
    hR hstrict hremaining htail
    (liveSingletonOptionShareScheduleSingleton_of_residualCaseNormalizedPointwiseRows
      hR hpayment)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseNormalizedLabelRowsDerivedSignComponents
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
                let paid :=
                  cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v
                let R := D - paid
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ i : ι Ωnz v x,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) i,
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_derivedSignComponents
    hR hstrict hremaining htail
    (liveSingletonOptionShareScheduleSingleton_of_residualCaseNormalizedLabelRows
      (schedule := schedule) (label := label) hR hpayment)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonPaymentDerivedSignComponents
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonPayment
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_derivedSignComponents
    hR hstrict hremaining htail
    (liveSingletonOptionShareScheduleSingleton_of_residualCaseShareBudget
      hsingletonResidual)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonFineComponents
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hremainingNonneg :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingNonnegativePositiveSubcritical
        schedule)
    (htailNonneg :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailNonnegativePositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule := by
  exact
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_fine_components
      hR hremainingNonneg htailNonneg
      (liveSingletonOptionShareScheduleSingletonNonnegative_of_residualCaseShareBudget
        hR hsingletonResidual)
      hstrict hremaining htail
      (liveSingletonOptionShareScheduleSingleton_of_residualCaseShareBudget
        (liveSingletonOptionShareScheduleResidualCaseSingletonPayment_of_denominatorNonnegativePayment
          hsingletonResidual))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonDerivedSignComponents
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      schedule :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonFineComponents
    hR
    (liveSingletonOptionShareScheduleRemainingNonnegative_of_remainingBound
      hR hremaining)
    (liveSingletonOptionShareScheduleTailNonnegative_of_tailBound
      hR htail)
    hstrict hremaining htail hsingletonResidual

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_shareSchedule
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  refine
    ⟨schedule.remainingShare β H Ωnz v,
      schedule.tailShare β H Ωnz v,
      fun x => schedule.singletonShare β H Ωnz v x, ?_⟩
  simpa [Ωnz] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_liveSingletonOptionComponentBudgetSchedule
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        budget) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_shareSchedule
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_liveSingletonOptionComponentBudgetSchedule
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hstrict⟩
  let singletonBudgetSum : ℝ := ∑ x ∈ liveOptions, singletonBudget x
  have hscalar : remaining + (singletonBudgetSum + tail) < R := by
    simpa [remaining, singletonBudgetSum, tail, R, liveOptions, Ωnz, cap, D,
      paid] using hstrict
  have hremainingNonneg : 0 ≤ remaining := by
    simpa [remaining] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have htailNonneg : 0 ≤ tail := by
    simpa [tail] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hbudgetNonneg :
      ∀ x ∈ liveOptions, 0 ≤ singletonBudget x := by
    intro x hx
    have hsourceNonneg :
        0 ≤
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v true true true ∪
          ({x} : Finset (Option (FK.boxVerts 3 n))))
    exact le_trans hsourceNonneg (hpoint x hx)
  have hbudgetSumNonneg : 0 ≤ singletonBudgetSum := by
    dsimp [singletonBudgetSum]
    exact Finset.sum_nonneg fun x hx => hbudgetNonneg x hx
  have hlhsNonneg : 0 ≤ remaining + (singletonBudgetSum + tail) := by
    exact add_nonneg hremainingNonneg
      (add_nonneg hbudgetSumNonneg htailNonneg)
  have hRpos : 0 < R := lt_of_le_of_lt hlhsNonneg hscalar
  refine
    ⟨remaining / R, tail / R, fun x => singletonBudget x / R,
      hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg hremainingNonneg (le_of_lt hRpos)
  · exact div_nonneg htailNonneg (le_of_lt hRpos)
  · intro x hx
    exact div_nonneg (hbudgetNonneg x hx) (le_of_lt hRpos)
  · change remaining ≤ (remaining / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change tail ≤ (tail / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · intro x hx
    change
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ωnz v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
        (singletonBudget x / R) * R
    exact le_trans (hpoint x hx) (le_of_eq (by field_simp [hRpos.ne']))
  · change
      remaining / R +
          ((∑ x ∈ liveOptions, singletonBudget x / R) + tail / R) <
        1
    have hscalar' :
        remaining + singletonBudgetSum + tail < R := by
      simpa [add_assoc] using hscalar
    have hratio :
        remaining / R + singletonBudgetSum / R + tail / R < 1 :=
      (three_ratio_sum_lt_one_iff_sum_lt_of_pos
        (one := remaining)
        (boundary := singletonBudgetSum)
        (empty := tail)
        hRpos).2 hscalar'
    have hsumDiv :
        (∑ x ∈ liveOptions, singletonBudget x / R) =
          singletonBudgetSum / R := by
      dsimp [singletonBudgetSum]
      rw [← Finset.sum_div]
    have hrewrite :
        remaining / R +
            ((∑ x ∈ liveOptions, singletonBudget x / R) + tail / R) =
          remaining / R + singletonBudgetSum / R + tail / R := by
      rw [hsumDiv]
      ring
    rw [hrewrite]
    exact hratio

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  rcases hn H hH Ω v hv with
    ⟨remainingShare, tailShare, singletonShare, hRpos,
      _hremainingShareNonneg, _htailShareNonneg, _hsingletonShareNonneg,
      hremaining, htail, hpoint, hshareStrict⟩
  refine ⟨fun x => singletonShare x * R, ?_, ?_⟩
  · intro x hx
    exact hpoint x hx
  · have hsumScale :
        (∑ x ∈ liveOptions, singletonShare x * R) =
          (∑ x ∈ liveOptions, singletonShare x) * R := by
      rw [Finset.sum_mul]
    have hcardTail :
        (∑ x ∈ liveOptions, singletonShare x * R) +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v ≤
          (∑ x ∈ liveOptions, singletonShare x) * R +
            tailShare * R := by
      exact add_le_add (le_of_eq hsumScale) htail
    have hmono :
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v +
          ((∑ x ∈ liveOptions, singletonShare x * R) +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) ≤
          remainingShare * R +
            ((∑ x ∈ liveOptions, singletonShare x) * R +
              tailShare * R) :=
      add_le_add hremaining hcardTail
    have hscaled :
        (remainingShare + ((∑ x ∈ liveOptions, singletonShare x) + tailShare)) *
            R <
          1 * R :=
      mul_lt_mul_of_pos_right hshareStrict hRpos
    have hstrict :
        remainingShare * R +
            ((∑ x ∈ liveOptions, singletonShare x) * R +
              tailShare * R) <
          D - paid := by
      calc
        remainingShare * R +
            ((∑ x ∈ liveOptions, singletonShare x) * R +
              tailShare * R)
            =
              (remainingShare +
                  ((∑ x ∈ liveOptions, singletonShare x) + tailShare)) *
                R := by
              ring
        _ < 1 * R := hscaled
        _ = D - paid := by
          simp [R]
    exact lt_of_le_of_lt hmono hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFree,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  rcases hn H hH Ω v hv with
    ⟨remainingShare, tailShare, singletonShare, hRpos,
      _hremainingShareNonneg, _htailShareNonneg, _hsingletonShareNonneg,
      hremaining, htail, hpoint, hshareStrict⟩
  have hcardLe :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v ≤
        ∑ x ∈ liveOptions, singletonShare x * R :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_singletonOptionNonemptyClassifiedSet_singletonBudget_sum_of_boundary
      hv hpoint
  have hcardTail :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v ≤
        (∑ x ∈ liveOptions, singletonShare x * R) + tailShare * R :=
    add_le_add hcardLe htail
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
            β H n Ωnz v +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        remainingShare * R +
          ((∑ x ∈ liveOptions, singletonShare x * R) + tailShare * R) :=
    add_le_add hremaining hcardTail
  have hsumScale :
      (∑ x ∈ liveOptions, singletonShare x * R) =
        (∑ x ∈ liveOptions, singletonShare x) * R := by
    rw [Finset.sum_mul]
  have hscaled :
      (remainingShare + ((∑ x ∈ liveOptions, singletonShare x) + tailShare)) *
          R <
        1 * R :=
    mul_lt_mul_of_pos_right hshareStrict hRpos
  have hstrict :
      remainingShare * R +
          ((∑ x ∈ liveOptions, singletonShare x * R) + tailShare * R) <
        D - paid := by
    calc
      remainingShare * R +
          ((∑ x ∈ liveOptions, singletonShare x * R) + tailShare * R)
          =
            (remainingShare +
                ((∑ x ∈ liveOptions, singletonShare x) + tailShare)) *
              R := by
            rw [hsumScale]
            ring
      _ < 1 * R := hscaled
      _ = D - paid := by
        simp [R]
  exact lt_of_le_of_lt hmono hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let singletonOptionSupportCount : ℝ := (liveOptions.card : ℝ)
  rcases hn H hH Ω v hv with
    ⟨remainingShare, singletonMaxCapShare, tailShare, hRpos,
      hremainingShareNonneg, hsingletonShareNonneg, htailShareNonneg,
      hremaining, hcapBound, htail, hshareStrict⟩
  refine
    ⟨remainingShare, tailShare, fun _ => singletonMaxCapShare,
      hRpos, hremainingShareNonneg, htailShareNonneg, ?_, hremaining,
      htail, ?_, ?_⟩
  · intro x _hx
    exact hsingletonShareNonneg
  · intro x hx
    have hxUnmarked :
        x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff.mp
        hx).1
    exact
      le_trans
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_pointwise
          β H n Ωnz hv x hxUnmarked)
        hcapBound
  · have hsum :
        (∑ x ∈ liveOptions, singletonMaxCapShare) =
          singletonOptionSupportCount * singletonMaxCapShare := by
      simp [singletonOptionSupportCount, liveOptions, Finset.sum_const,
        nsmul_eq_mul]
    simpa [singletonOptionSupportCount, liveOptions, hsum] using hshareStrict

end Exact3D
end StatMech
