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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part141
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryCoefficientPayment_of_positiveRatioPayment
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
      q := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let R := (β * H) / Real.tanh (β * H)
  let Q := q β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change R * Q ≤ D / 3
  have hRpos : 0 < R := by
    simpa [R] using
      div_pos (mul_pos hβpos hH)
        (real_tanh_pos_of_pos (mul_pos hβpos hH))
  have hbudget : Q ≤ (D / 3) / R := by
    simpa [R, Q, D] using hnpay H hH Ω v hv
  calc
    R * Q ≤ R * ((D / 3) / R) :=
      mul_le_mul_of_nonneg_left hbudget (le_of_lt hRpos)
    _ = D / 3 := by
      field_simp [ne_of_gt hRpos]

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryCoefficientPayment_allowedSourcePairBudget :
    BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
      boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget :=
  boxRatioEmptyBoundaryCoefficientPayment_of_positiveRatioPayment
    boxRatioEmptyBoundaryCoefficientPositiveRatioPayment_allowedSourcePairBudget

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryCoefficientPositiveRatioPayment_of_payment
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
      q := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let R := (β * H) / Real.tanh (β * H)
  let Q := q β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change Q ≤ (D / 3) / R
  have hRpos : 0 < R := by
    simpa [R] using
      div_pos (mul_pos hβpos hH)
        (real_tanh_pos_of_pos (mul_pos hβpos hH))
  have hmul : Q * R ≤ D / 3 := by
    simpa [R, Q, D, mul_comm] using hnpay H hH Ω v hv
  exact (le_div_iff₀ hRpos).2 hmul

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryCoefficientPositiveRatioPayment_iff_payment
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget} :
    BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q ↔
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
        q :=
  ⟨boxRatioEmptyBoundaryCoefficientPayment_of_positiveRatioPayment,
    boxRatioEmptyBoundaryCoefficientPositiveRatioPayment_of_payment⟩

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundarySourcePairComparison_of_ratioComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
      q := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hncmp
  intro H hH Ω v hv
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let E := edgeCopySourcePairEmptyCollapsedSum G β J A
  let E0 := edgeCopySourcePairEmptyCollapsedSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let Q := q β H n v
  change E ≤ Q * E0
  have hE0pos : 0 < E0 := by
    simpa [G, J, E0] using
      edgeCopySourcePairEmptyCollapsedSum_empty_pos G β J
  have hratio : E / E0 ≤ Q := by
    simpa [G, J, A, E, E0, Q] using hncmp H hH Ω v hv
  exact (div_le_iff₀ hE0pos).mp hratio

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundarySourcePairRatioComparison_of_comparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
      q := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hncmp
  intro H hH Ω v hv
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let E := edgeCopySourcePairEmptyCollapsedSum G β J A
  let E0 := edgeCopySourcePairEmptyCollapsedSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let Q := q β H n v
  change E / E0 ≤ Q
  have hE0pos : 0 < E0 := by
    simpa [G, J, E0] using
      edgeCopySourcePairEmptyCollapsedSum_empty_pos G β J
  have hmul : E ≤ Q * E0 := by
    simpa [G, J, A, E, E0, Q] using hncmp H hH Ω v hv
  rw [div_le_iff₀ hE0pos]
  exact hmul

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundarySourcePairRatioComparison_iff_comparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget} :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q ↔
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
        q :=
  ⟨boxRatioEmptyBoundarySourcePairComparison_of_ratioComparison,
    boxRatioEmptyBoundarySourcePairRatioComparison_of_comparison⟩

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPayment_sourcePairComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc, hcmp β hβpos hβc] with
    n hnpay hncmp
  intro H hH Ω v hv
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let E := edgeCopySourcePairEmptyCollapsedSum G β J A
  let E0 := edgeCopySourcePairEmptyCollapsedSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let Q := q β H n v
  let R := (β * H) / Real.tanh (β * H)
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change R * E ≤ (D / 3) * E0
  have hcmpLe : E ≤ Q * E0 := by
    simpa [G, J, A, E, E0, Q] using hncmp H hH Ω v hv
  have hpayLe : R * Q ≤ D / 3 := by
    simpa [R, Q, D] using hnpay H hH Ω v hv
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hHnonneg : 0 ≤ H := le_of_lt hH
  have hJ : ∀ e, 0 ≤ J e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary 3 n) hHnonneg
      (fun _ => by norm_num)
  have hTnonneg : 0 ≤ Real.tanh (β * H) :=
    le_of_lt (real_tanh_pos_of_pos (mul_pos hβpos hH))
  have hRnonneg : 0 ≤ R := by
    simpa [R] using
      div_nonneg (mul_nonneg hβnonneg hHnonneg) hTnonneg
  have hE0nonneg : 0 ≤ E0 := by
    simpa [G, J, E0] using
      edgeCopySourcePairEmptyCollapsedSum_nonneg G β J
        (∅ : Finset (Option (FK.boxVerts 3 n))) hβnonneg hJ
  calc
    R * E ≤ R * (Q * E0) :=
      mul_le_mul_of_nonneg_left hcmpLe hRnonneg
    _ = (R * Q) * E0 := by ring
    _ ≤ (D / 3) * E0 :=
      mul_le_mul_of_nonneg_right hpayLe hE0nonneg

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPayment_sourcePairRatioComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPayment_sourcePairComparison
    hpay
    (boxRatioEmptyBoundarySourcePairComparison_of_ratioComparison hcmp)

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPositiveRatioPayment_sourcePairRatioComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPayment_sourcePairRatioComparison
    (boxRatioEmptyBoundaryCoefficientPayment_of_positiveRatioPayment hpay)
    hcmp

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryCurrentSumThird_of_emptyCollapsedThird
    (hempty :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryCurrentSumThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hempty β hβpos hβc] with n hnempty
  intro H hH Ω v hv
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let R := (β * H) / Real.tanh (β * H)
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hcollapsed :
      R * (ZA * Z0) ≤ (D / 3) * (Z0 * Z0) := by
    simpa [
      G, J, A, Z0, ZA, R, D,
      edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul] using
      hnempty H hH Ω v hv
  have hcancel :
      (R * ZA) * Z0 ≤ ((D / 3) * Z0) * Z0 := by
    calc
      (R * ZA) * Z0 = R * (ZA * Z0) := by ring
      _ ≤ (D / 3) * (Z0 * Z0) := hcollapsed
      _ = ((D / 3) * Z0) * Z0 := by ring
  have hdiv :
      ((R * ZA) * Z0) / Z0 ≤ (((D / 3) * Z0) * Z0) / Z0 :=
    div_le_div_of_nonneg_right hcancel (le_of_lt hZ0pos)
  calc
    R * ZA = ((R * ZA) * Z0) / Z0 := by
      field_simp [ne_of_gt hZ0pos]
    _ ≤ (((D / 3) * Z0) * Z0) / Z0 := hdiv
    _ = (D / 3) * Z0 := by
      field_simp [ne_of_gt hZ0pos]

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_currentSumThird
    (hempty :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCurrentSumThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hempty β hβpos hβc] with n hnempty
  intro H hH Ω v hv
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1)
  let A : Finset (Option (FK.boxVerts 3 n)) :=
    ({some (IsingFK.boxOrigin 3 n)} :
      Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
  let Z0 := Sharpness.currentSum G β J
    (∅ : Finset (Option (FK.boxVerts 3 n)))
  let ZA := Sharpness.currentSum G β J A
  let R := (β * H) / Real.tanh (β * H)
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hZ0pos : 0 < Z0 := by
    simpa [G, J, Z0] using currentSum_empty_pos G β J
  have hsum : R * ZA ≤ (D / 3) * Z0 := by
    simpa [G, J, A, Z0, ZA, R, D] using hnempty H hH Ω v hv
  have hratio : (R * ZA) / Z0 ≤ D / 3 := by
    rw [div_le_iff₀ hZ0pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsum
  change R * (ZA / Z0) ≤ D / 3
  calc
    R * (ZA / Z0) = (R * ZA) / Z0 := by
      field_simp [ne_of_gt hZ0pos]
    _ ≤ D / 3 := hratio

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_emptyCollapsedThird
    (hempty :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryThird_of_currentSumThird
    (boxRatioEmptyBoundaryCurrentSumThird_of_emptyCollapsedThird hempty)

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_coefficientPayment_sourcePairComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryThird_of_emptyCollapsedThird
    (boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPayment_sourcePairComparison
      hpay hcmp)

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_coefficientPositiveRatioPayment_sourcePairComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryThird_of_coefficientPayment_sourcePairComparison
    (boxRatioEmptyBoundaryCoefficientPayment_of_positiveRatioPayment hpay)
    hcmp

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_coefficientPayment_sourcePairRatioComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryThird_of_emptyCollapsedThird
    (boxRatioEmptyBoundaryEmptyCollapsedThird_of_coefficientPayment_sourcePairRatioComparison
      hpay hcmp)

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_coefficientPositiveRatioPayment_sourcePairRatioComparison
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryThird_of_coefficientPayment_sourcePairRatioComparison
    (boxRatioEmptyBoundaryCoefficientPayment_of_positiveRatioPayment hpay)
    hcmp

set_option linter.style.longLine false in


theorem boxRatioEmptyBoundaryThird_of_allowedSourcePairRatioComparison
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :=
  boxRatioEmptyBoundaryThird_of_coefficientPositiveRatioPayment_sourcePairRatioComparison
    boxRatioEmptyBoundaryCoefficientPositiveRatioPayment_allowedSourcePairBudget
    hcmp


end Exact3D
end StatMech
