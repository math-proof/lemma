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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part97
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment_of_canonical :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment_of_rowSumSchedule
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedRemainingShare (n := n) β H Ω v)
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedTailShare (n := n) β H Ω v)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment_of_canonical
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    (label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
      label
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label) :=
  liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment_of_rowSumSchedule
    label
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedRemainingShare (n := n) β H Ω v)
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedTailShare (n := n) β H Ω v)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleRemaining_of_residualCaseNormalizedPointwiseRowsCanonical
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc] with n hnR
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
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hEq :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v =
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v / R) * R := by
    rw [div_mul_cancel₀ _ hRpos.ne']
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
    liveSingletonOptionNormalizedRemainingShare, Ωnz, cap, D, paid, R] using
    le_of_eq hEq

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleTail_of_residualCaseNormalizedPointwiseRowsCanonical
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc] with n hnR
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
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hEq :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v =
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v / R) * R := by
    rw [div_mul_cancel₀ _ hRpos.ne']
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
    liveSingletonOptionNormalizedTailShare, Ωnz, cap, D, paid, R] using
    le_of_eq hEq

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleRemaining_of_residualCaseNormalizedLabelRowsCanonical
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
          label)) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label) := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc] with n hnR
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
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hEq :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v =
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v / R) * R := by
    rw [div_mul_cancel₀ _ hRpos.ne']
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows,
    liveSingletonOptionNormalizedRemainingShare, Ωnz, cap, D, paid, R] using
    le_of_eq hEq

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleTail_of_residualCaseNormalizedLabelRowsCanonical
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
          label)) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label) := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc] with n hnR
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
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hEq :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v =
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v / R) * R := by
    rw [div_mul_cancel₀ _ hRpos.ne']
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows,
    liveSingletonOptionNormalizedTailShare, Ωnz, cap, D, paid, R] using
    le_of_eq hEq

set_option linter.style.longLine false in


theorem liveSingletonOptionStrictTotalShare_lt_one_of_rawNumerator_lt
    {α : Type*} (liveOptions : Finset α) (R remaining tail : ℝ)
    (row : α → ℝ) (hRpos : 0 < R)
    (hraw :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) < R) :
    remaining / R + ((∑ x ∈ liveOptions, row x / R) + tail / R) < 1 := by
  have hEq :
      remaining / R + ((∑ x ∈ liveOptions, row x / R) + tail / R) =
        (remaining + ((∑ x ∈ liveOptions, row x) + tail)) / R := by
    simp_rw [← Finset.sum_div]
    field_simp [hRpos.ne']
  calc
    remaining / R + ((∑ x ∈ liveOptions, row x / R) + tail / R) =
        (remaining + ((∑ x ∈ liveOptions, row x) + tail)) / R := hEq
    _ < 1 := (div_lt_one hRpos).2 hraw

set_option linter.style.longLine false in

theorem finset_sum_div_mul_cancel₀ {α : Type*} (s : Finset α)
    (f : α → ℝ) {R : ℝ} (hR : R ≠ 0) :
    (∑ x ∈ s, f x / R) * R = ∑ x ∈ s, f x := by
  rw [← Finset.sum_div]
  exact div_mul_cancel₀ _ hR

end Exact3D
end StatMech
