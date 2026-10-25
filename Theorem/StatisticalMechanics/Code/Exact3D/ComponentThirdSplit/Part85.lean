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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part90
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorption_of_liveSingletonOptionShareSchedule
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        schedule) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      (liveSingletonOptionComponentBudgetScheduleOfShareSchedule schedule) := by
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
    ⟨hRpos, _hremainingShareNonneg, _htailShareNonneg,
      _hsingletonShareNonneg, hremaining, htail, hpoint,
      hshareStrict⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [liveSingletonOptionComponentBudgetScheduleOfShareSchedule, Ωnz,
      cap, D, paid, R] using hremaining
  · simpa [liveSingletonOptionComponentBudgetScheduleOfShareSchedule, Ωnz,
      cap, D, paid, R] using htail
  · intro x hx
    simpa [liveSingletonOptionComponentBudgetScheduleOfShareSchedule, Ωnz,
      cap, D, paid, R] using hpoint x hx
  · have hsumScale :
        (∑ x ∈ liveOptions,
            schedule.singletonShare β H Ωnz v x * R) =
          (∑ x ∈ liveOptions,
              schedule.singletonShare β H Ωnz v x) * R := by
      rw [Finset.sum_mul]
    have hscaled :
        (schedule.remainingShare β H Ωnz v +
            ((∑ x ∈ liveOptions,
                schedule.singletonShare β H Ωnz v x) +
              schedule.tailShare β H Ωnz v)) *
            R <
          1 * R :=
      mul_lt_mul_of_pos_right hshareStrict hRpos
    have hstrict :
        schedule.remainingShare β H Ωnz v * R +
            ((∑ x ∈ liveOptions,
                schedule.singletonShare β H Ωnz v x * R) +
              schedule.tailShare β H Ωnz v * R) <
          D - paid := by
      calc
        schedule.remainingShare β H Ωnz v * R +
            ((∑ x ∈ liveOptions,
                schedule.singletonShare β H Ωnz v x * R) +
              schedule.tailShare β H Ωnz v * R)
            =
              schedule.remainingShare β H Ωnz v * R +
                ((∑ x ∈ liveOptions,
                    schedule.singletonShare β H Ωnz v x) * R +
                  schedule.tailShare β H Ωnz v * R) := by
              rw [hsumScale]
        _ =
              (schedule.remainingShare β H Ωnz v +
                  ((∑ x ∈ liveOptions,
                      schedule.singletonShare β H Ωnz v x) +
                    schedule.tailShare β H Ωnz v)) *
                R := by
              ring
        _ < 1 * R := hscaled
        _ = D - paid := by
          simp [R]
    simpa [liveSingletonOptionComponentBudgetScheduleOfShareSchedule, Ωnz,
      cap, D, paid, R] using hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_liveSingletonOptionComponentBudgetSchedule
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        budget) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
      (liveSingletonOptionShareScheduleOfComponentBudgetSchedule budget) := by
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
  let remainingBudget := budget.remainingBudget β H Ωnz v
  let tailBudget := budget.tailBudget β H Ωnz v
  let singletonBudget := budget.singletonBudget β H Ωnz v
  let singletonBudgetSum : ℝ := ∑ x ∈ liveOptions, singletonBudget x
  rcases hn H hH Ω v hv with
    ⟨hremaining, htail, hsingleton, hpayment⟩
  have hremainingActualNonneg : 0 ≤ remaining := by
    simpa [remaining] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have htailActualNonneg : 0 ≤ tail := by
    simpa [tail] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hremainingBudgetNonneg : 0 ≤ remainingBudget := by
    exact le_trans hremainingActualNonneg
      (by
        simpa [remaining, remainingBudget, Ωnz] using hremaining)
  have htailBudgetNonneg : 0 ≤ tailBudget := by
    exact le_trans htailActualNonneg
      (by
        simpa [tail, tailBudget, Ωnz] using htail)
  have hsingletonBudgetNonneg :
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
    exact le_trans hsourceNonneg
      (by
        simpa [singletonBudget, liveOptions, Ωnz] using hsingleton x hx)
  have hsingletonBudgetSumNonneg : 0 ≤ singletonBudgetSum := by
    dsimp [singletonBudgetSum]
    exact Finset.sum_nonneg fun x hx => hsingletonBudgetNonneg x hx
  have hscalar :
      remainingBudget + (singletonBudgetSum + tailBudget) < R := by
    simpa [remainingBudget, singletonBudget, singletonBudgetSum, tailBudget,
      liveOptions, Ωnz, cap, D, paid, R] using hpayment
  have hlhsNonneg :
      0 ≤ remainingBudget + (singletonBudgetSum + tailBudget) := by
    exact add_nonneg hremainingBudgetNonneg
      (add_nonneg hsingletonBudgetSumNonneg htailBudgetNonneg)
  have hRpos : 0 < R := lt_of_le_of_lt hlhsNonneg hscalar
  refine
    ⟨hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 ≤ remainingBudget / R
    exact div_nonneg hremainingBudgetNonneg (le_of_lt hRpos)
  · change 0 ≤ tailBudget / R
    exact div_nonneg htailBudgetNonneg (le_of_lt hRpos)
  · intro x hx
    change 0 ≤ singletonBudget x / R
    exact div_nonneg (hsingletonBudgetNonneg x hx) (le_of_lt hRpos)
  · change remaining ≤ (remainingBudget / R) * R
    have hcancel : remainingBudget ≤ (remainingBudget / R) * R := by
      rw [div_mul_cancel₀ _ hRpos.ne']
    exact le_trans
      (by simpa [remaining, remainingBudget, Ωnz] using hremaining)
      hcancel
  · change tail ≤ (tailBudget / R) * R
    have hcancel : tailBudget ≤ (tailBudget / R) * R := by
      rw [div_mul_cancel₀ _ hRpos.ne']
    exact le_trans
      (by simpa [tail, tailBudget, Ωnz] using htail)
      hcancel
  · intro x hx
    change
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ωnz v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
        (singletonBudget x / R) * R
    have hcancel : singletonBudget x ≤ (singletonBudget x / R) * R := by
      rw [div_mul_cancel₀ _ hRpos.ne']
    exact le_trans
      (by simpa [singletonBudget, liveOptions, Ωnz] using hsingleton x hx)
      hcancel
  · change
      remainingBudget / R +
          ((∑ x ∈ liveOptions, singletonBudget x / R) +
            tailBudget / R) <
        1
    have hscalar' :
        remainingBudget + singletonBudgetSum + tailBudget < R := by
      simpa [add_assoc] using hscalar
    have hratio :
        remainingBudget / R + singletonBudgetSum / R +
            tailBudget / R < 1 :=
      (three_ratio_sum_lt_one_iff_sum_lt_of_pos
        (one := remainingBudget)
        (boundary := singletonBudgetSum)
        (empty := tailBudget)
        hRpos).2 hscalar'
    have hsumDiv :
        (∑ x ∈ liveOptions, singletonBudget x / R) =
          singletonBudgetSum / R := by
      dsimp [singletonBudgetSum]
      rw [← Finset.sum_div]
    have hrewrite :
        remainingBudget / R +
            ((∑ x ∈ liveOptions, singletonBudget x / R) +
              tailBudget / R) =
          remainingBudget / R + singletonBudgetSum / R +
            tailBudget / R := by
      rw [hsumDiv]
      ring
    rw [hrewrite]
    exact hratio

end Exact3D
end StatMech
