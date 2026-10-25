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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part148
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOneBoundaryCombinedTwoThirdUncutoff_of_components
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOneBoundaryCombinedTwoThirdUncutoffPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc, hboundary β hβpos hβc] with
    n hnone hnboundary
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have honeLe : cap * oneTerm ≤ D / 3 := by
    simpa [cap, oneTerm, D] using hnone H hH Ω v hv
  have hboundaryLe : cap * boundaryTerm ≤ D / 3 := by
    simpa [cap, boundaryTerm, D] using hnboundary H hH Ω v hv
  calc
    cap * (oneTerm + boundaryTerm) = cap * oneTerm + cap * boundaryTerm := by
      ring
    _ ≤ 2 * D / 3 := by
      linarith

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_of_combinedTwoThird_emptyThird
    (hcombined :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOneBoundaryCombinedTwoThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcombined β hβpos hβc, hempty β hβpos hβc] with
    n hncombined hnempty
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcombinedLe :
      cap * (oneTerm + boundaryTerm) ≤ 2 * D / 3 := by
    simpa [cap, oneTerm, boundaryTerm, D] using
      hncombined H hH Ω v hv
  have hcombinedShare :
      cap * (oneTerm + boundaryTerm) ≤ (2 / 3 : ℝ) * D := by
    calc
      cap * (oneTerm + boundaryTerm) ≤ 2 * D / 3 := hcombinedLe
      _ = (2 / 3 : ℝ) * D := by
        ring
  have hemptyLe : emptyTerm ≤ D / 3 := by
    simpa [emptyTerm, D] using hnempty H hH Ω v hv
  have hemptyShare : emptyTerm ≤ (1 / 3 : ℝ) * D := by
    calc
      emptyTerm ≤ D / 3 := hemptyLe
      _ = (1 / 3 : ℝ) * D := by
        ring
  exact
    ⟨2 / 3, 1 / 3, by norm_num, by norm_num, by norm_num,
      hcombinedShare, hemptyShare⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_of_components
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_of_combinedTwoThird_emptyThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOneBoundaryCombinedTwoThirdUncutoff_of_components
      hone hboundary)
    hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_combinedEmptyShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hshare β hβpos hβc] with n hnshare
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hnshare H hH Ω v hv with
    ⟨combinedShare, emptyShare, _hcombinedShareNonneg, _hemptyShareNonneg,
      hshareSum, hcombinedLe, hemptyLe⟩
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  calc
    cap * (oneTerm + boundaryTerm) + emptyTerm ≤
        combinedShare * D + emptyShare * D := by
      exact add_le_add hcombinedLe hemptyLe
    _ = (combinedShare + emptyShare) * D := by
      ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hshareSum hD
    _ = D := by
      ring

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_of_componentSumUncutoffCombined
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hsum β hβpos hβc] with n hnsum
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let combined := cap * (oneTerm + boundaryTerm)
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  have hcap : 0 ≤ cap := by
    simpa [cap] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_nonneg
        β H Ω
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have hcombinedTerm : 0 ≤ oneTerm + boundaryTerm :=
    add_nonneg honeTerm hboundaryTerm
  have hcombined : 0 ≤ combined :=
    mul_nonneg hcap hcombinedTerm
  have hemptyTerm : 0 ≤ emptyTerm := by
    simpa [emptyTerm] using
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm_nonneg
        v hβpos hH
  have hsum' : combined + emptyTerm ≤ D := by
    simpa [combined, cap, oneTerm, boundaryTerm, emptyTerm, D] using
      hnsum H hH Ω v hv
  rcases twoShares_of_nonneg_sum_le hD hcombined hemptyTerm hsum' with
    ⟨combinedShare, emptyShare, hcombinedShareNonneg, hemptyShareNonneg,
      hshareSum, hcombinedLe, hemptyLe⟩
  exact
    ⟨combinedShare, emptyShare, hcombinedShareNonneg, hemptyShareNonneg,
      hshareSum,
      by simpa [combined, cap, oneTerm, boundaryTerm, D] using hcombinedLe,
      by simpa [emptyTerm, D] using hemptyLe⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_iff_componentSumUncutoffCombined :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_combinedEmptyShare,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_of_componentSumUncutoffCombined⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_componentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hshare β hβpos hβc] with n hnshare
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hnshare H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, _honeShareNonneg,
      _hboundaryShareNonneg, _hemptyShareNonneg, hshareSum, honeLe,
      hboundaryLe, hemptyLe⟩
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  calc
    cap * (oneTerm + boundaryTerm) + emptyTerm =
        cap * oneTerm + cap * boundaryTerm + emptyTerm := by
      ring
    _ ≤ oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D := by
      linarith
    _ = (oneShare + boundaryPairShare + emptyBoundaryShare) * D := by
      ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hshareSum hD
    _ = D := by
      ring

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_of_componentSumUncutoffCombined
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hsum β hβpos hβc] with n hnsum
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let one := cap * oneTerm
  let boundary := cap * boundaryTerm
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  have hcap : 0 ≤ cap := by
    simpa [cap] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_nonneg
        β H Ω
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have hone : 0 ≤ one :=
    mul_nonneg hcap honeTerm
  have hboundary : 0 ≤ boundary :=
    mul_nonneg hcap hboundaryTerm
  have hemptyTerm : 0 ≤ emptyTerm := by
    simpa [emptyTerm] using
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm_nonneg
        v hβpos hH
  have hsumCombined :
      cap * (oneTerm + boundaryTerm) + emptyTerm ≤ D := by
    simpa [cap, oneTerm, boundaryTerm, emptyTerm, D] using
      hnsum H hH Ω v hv
  have hsum' : one + boundary + emptyTerm ≤ D := by
    calc
      one + boundary + emptyTerm =
          cap * (oneTerm + boundaryTerm) + emptyTerm := by
        ring
      _ ≤ D := hsumCombined
  rcases componentShares_of_nonneg_sum_le hD hone hboundary hemptyTerm hsum' with
    ⟨oneShare, boundaryShare, emptyShare, honeShare, hboundaryShare,
      hemptyShare, hshareSum, honeLe, hboundaryLe, hemptyLe⟩
  exact
    ⟨oneShare, boundaryShare, emptyShare, honeShare, hboundaryShare,
      hemptyShare, hshareSum,
      by simpa [one, cap, oneTerm, D] using honeLe,
      by simpa [boundary, cap, boundaryTerm, D] using hboundaryLe,
      by simpa [emptyTerm, D] using hemptyLe⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_iff_componentSumUncutoffCombined :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_componentShareUncutoff,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_of_componentSumUncutoffCombined⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_of_schedule
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  exact ⟨capBudget β H n Ω v, hn H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetUncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let emptyTerm :=
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hn H hH Ω v hv with ⟨capBudget, hcap, hbudget⟩
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have hcombined : 0 ≤ oneTerm + boundaryTerm :=
    add_nonneg honeTerm hboundaryTerm
  have hmul :
      cap * (oneTerm + boundaryTerm) ≤
        capBudget * (oneTerm + boundaryTerm) :=
    mul_le_mul_of_nonneg_right (by simpa [cap] using hcap) hcombined
  have hbudget' :
      capBudget * (oneTerm + boundaryTerm) + emptyTerm ≤ D := by
    simpa [oneTerm, boundaryTerm, emptyTerm, D] using hbudget
  calc
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω *
          (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
            boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v) +
        boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v =
        cap * (oneTerm + boundaryTerm) + emptyTerm := by
      rfl
    _ ≤ capBudget * (oneTerm + boundaryTerm) + emptyTerm :=
      add_le_add hmul (le_refl emptyTerm)
    _ ≤ D := hbudget'

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_of_componentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  refine
    ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω,
      le_rfl, ?_⟩
  simpa using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_iff_componentSumUncutoffCombined :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetUncutoff,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_of_componentSumUncutoffCombined⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetScheduleUncutoff
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetUncutoff
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_of_schedule
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_of_cardSummandBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {summandBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummandBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSummandBudgetScheduleUncutoffPositiveSubcritical
        cardBudget summandBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
      (fun β H n Ω v => cardBudget β H n Ω v * summandBudget β H n Ω v) := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨hcard, hsummandBudgetNonneg, hsummand, hbudget⟩
  constructor
  · have hcapCard :
        boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
          (Ω.card : ℝ) * summandBudget β H n Ω v := by
      exact
        boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_card_mul_of_summand_le
          (β := β) (H := H) (Ω := Ω) hsummand
    have hcardBudget :
        (Ω.card : ℝ) * summandBudget β H n Ω v ≤
          cardBudget β H n Ω v * summandBudget β H n Ω v :=
      mul_le_mul_of_nonneg_right hcard hsummandBudgetNonneg
    exact le_trans hcapCard hcardBudget
  · exact hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSummandBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {summandBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummandBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSummandBudgetScheduleUncutoffPositiveSubcritical
        cardBudget summandBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetScheduleUncutoff
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_of_cardSummandBudgetSchedule
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSummandBudgetScheduleUncutoff_of_cardSourceMultiplicityBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {multiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostMultiplicityBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceMultiplicityBudgetScheduleUncutoffPositiveSubcritical
        cardBudget sourceCardBudget multiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSummandBudgetScheduleUncutoffPositiveSubcritical
      cardBudget
      (fun β H n Ω v =>
        sourceCardBudget β H n Ω v *
          multiplicityBudget β H n Ω v *
          multiplicityBudget β H n Ω v) := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨hcard, hsourceBudgetNonneg, hmultBudgetNonneg, hsource, hmult,
      hbudget⟩
  refine ⟨hcard, ?_, ?_, hbudget⟩
  · exact
      mul_nonneg
        (mul_nonneg hsourceBudgetNonneg hmultBudgetNonneg)
        hmultBudgetNonneg
  · intro m hm
    exact
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_le_sourceCard_mul_multiplicityBudget_sq
        (n := n) m (hsource m hm) (hmult m hm)
        hsourceBudgetNonneg hmultBudgetNonneg

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSourceMultiplicityBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {multiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostMultiplicityBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceMultiplicityBudgetScheduleUncutoffPositiveSubcritical
        cardBudget sourceCardBudget multiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSummandBudgetSchedule
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSummandBudgetScheduleUncutoff_of_cardSourceMultiplicityBudgetSchedule
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceMultiplicityBudgetScheduleUncutoff_of_cardSourceBoundaryEdgeBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {boundaryVertexBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryVertexBudgetSchedule}
    {edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeBudgetScheduleUncutoffPositiveSubcritical
        cardBudget sourceCardBudget boundaryVertexBudget edgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceMultiplicityBudgetScheduleUncutoffPositiveSubcritical
      cardBudget sourceCardBudget
      (fun β H n Ω v =>
        boundaryVertexBudget β H n Ω v *
          edgeMultiplicityBudget β H n Ω v) := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨hcard, hsourceBudgetNonneg, hboundaryVertexBudgetNonneg,
      hedgeBudgetNonneg, hboundaryCard, hsource, hedge, hbudget⟩
  refine ⟨hcard, hsourceBudgetNonneg, ?_, hsource, ?_, hbudget⟩
  · exact
      mul_nonneg hboundaryVertexBudgetNonneg hedgeBudgetNonneg
  · intro m hm
    have hsum :
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
          (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            edgeMultiplicityBudget β H n Ω v) :=
      finiteBoundaryGhostBoundaryGhostMultiplicitySum_le_boundaryCard_mul_of_edgeMultiplicity_le
        (n := n) m (hedge m hm)
    have hbudgetLe :
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            edgeMultiplicityBudget β H n Ω v) ≤
          boundaryVertexBudget β H n Ω v *
            edgeMultiplicityBudget β H n Ω v :=
      mul_le_mul_of_nonneg_right hboundaryCard hedgeBudgetNonneg
    exact le_trans hsum hbudgetLe

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSourceBoundaryEdgeBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {boundaryVertexBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryVertexBudgetSchedule}
    {edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeBudgetScheduleUncutoffPositiveSubcritical
        cardBudget sourceCardBudget boundaryVertexBudget edgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSourceMultiplicityBudgetSchedule
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceMultiplicityBudgetScheduleUncutoff_of_cardSourceBoundaryEdgeBudgetSchedule
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeBudgetScheduleUncutoff_of_cardSourceBoundaryEdgeActualBoundarySchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeActualBoundaryScheduleUncutoffPositiveSubcritical
        cardBudget sourceCardBudget edgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeBudgetScheduleUncutoffPositiveSubcritical
      cardBudget sourceCardBudget
      (fun _β _H n _Ω _v =>
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)))
      edgeMultiplicityBudget := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨hcard, hsourceBudgetNonneg, hedgeBudgetNonneg, hsource, hedge,
      hbudget⟩
  refine
    ⟨hcard, hsourceBudgetNonneg, ?_, hedgeBudgetNonneg, le_rfl, hsource,
      hedge, ?_⟩
  · exact Nat.cast_nonneg _
  · simpa using hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSourceBoundaryEdgeActualBoundarySchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeActualBoundaryScheduleUncutoffPositiveSubcritical
        cardBudget sourceCardBudget edgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSourceBoundaryEdgeBudgetSchedule
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeBudgetScheduleUncutoff_of_cardSourceBoundaryEdgeActualBoundarySchedule
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeActualBoundaryScheduleUncutoff_of_aggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeActualBoundaryScheduleUncutoffPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule]
  · simpa [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  · simpa [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ω,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  · intro m hm
    simpa [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule] using
      finiteBoundaryGhostSourceSector_card_le_cutoff_sourceSector_card_sum
        (n := n) (Ω := Ω) (m := m) hm
  · intro m hm w hw
    simpa [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      finiteBoundaryGhostBoundaryEdgeMultiplicity_le_cutoff_boundaryEdge_sum
        (n := n) (Ω := Ω) (m := m) hm (w := w) hw
  · simpa [
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarUncutoffPositiveSubcritical,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_aggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_cardSourceBoundaryEdgeActualBoundarySchedule
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeActualBoundaryScheduleUncutoff_of_aggregateEnvelopeActualBoundaryScalar
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalar_of_twoThird_emptyThird
    (haggregate :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [haggregate β hβpos hβc, hempty β hβpos hβc] with
    n hnaggregate hnempty
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cardBudget := (Ωnz.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ωnz,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  let aggregateBudget :=
    cardBudget *
      (sourceCardBudget * (boundaryCard * edgeBudget) *
        (boundaryCard * edgeBudget))
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let emptyTerm :=
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have haggregateLe :
      aggregateBudget * (oneTerm + boundaryTerm) ≤ 2 * D / 3 := by
    exact hnaggregate H hH Ω v hv
  have hemptyLe : emptyTerm ≤ D / 3 := by
    simpa [emptyTerm, D] using hnempty H hH Ω v hv
  calc
    (cardBudget *
          (sourceCardBudget * (boundaryCard * edgeBudget) *
            (boundaryCard * edgeBudget))) *
          (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
            boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
              β H n v) +
        boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v =
        aggregateBudget * (oneTerm + boundaryTerm) + emptyTerm := by
      rfl
    _ ≤ 2 * D / 3 + D / 3 := add_le_add haggregateLe hemptyLe
    _ = D := by
      ring

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_components
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc, hboundary β hβpos hβc] with
    n hnone hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cardBudget := (Ωnz.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ωnz,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  let aggregateBudget :=
    cardBudget *
      (sourceCardBudget * (boundaryCard * edgeBudget) *
        (boundaryCard * edgeBudget))
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have honeLe : aggregateBudget * oneTerm ≤ D / 3 := by
    exact hnone H hH Ω v hv
  have hboundaryLe : aggregateBudget * boundaryTerm ≤ D / 3 := by
    exact hnboundary H hH Ω v hv
  calc
    (cardBudget *
          (sourceCardBudget * (boundaryCard * edgeBudget) *
            (boundaryCard * edgeBudget))) *
        (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
          boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
            β H n v) =
        aggregateBudget * oneTerm + aggregateBudget * boundaryTerm := by
      ring
    _ ≤ 2 * D / 3 := by
      linarith

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_positiveRatioResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  by_cases hzero : oneTerm = 0
  · exact Or.inl hzero
  · have htermNonneg : 0 ≤ oneTerm := by
      simpa [oneTerm] using
        boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) hβpos hH
    have htermPos : 0 < oneTerm :=
      lt_of_le_of_ne htermNonneg (Ne.symm hzero)
    exact Or.inr (by
      simpa [Ωnz, aggregateBudget, oneTerm] using
        hnone H hH Ω v hv htermPos)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_positiveRatioResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  by_cases hzero : boundaryTerm = 0
  · exact Or.inl hzero
  · have htermNonneg : 0 ≤ boundaryTerm := by
      simpa [boundaryTerm] using
        boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) v hβpos hH
    have htermPos : 0 < boundaryTerm :=
      lt_of_le_of_ne htermNonneg (Ne.symm hzero)
    exact Or.inr (by
      simpa [Ωnz, aggregateBudget, boundaryTerm] using
        hnboundary H hH Ω v hv htermPos)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_residualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  change
    0 < oneTerm →
      aggregateBudget ≤
        (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm
  intro htermPos
  have hres :
      oneTerm = 0 ∨
        aggregateBudget ≤
          (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm := by
    simpa [Ωnz, aggregateBudget, oneTerm] using hnone H hH Ω v hv
  rcases hres with hzero | hbudget
  · exact False.elim (ne_of_gt htermPos hzero)
  · exact hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_residualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  change
    0 < boundaryTerm →
      aggregateBudget ≤
        (boundaryVertexBoxSimonCurrentRatio β n v / 3) / boundaryTerm
  intro htermPos
  have hres :
      boundaryTerm = 0 ∨
        aggregateBudget ≤
          (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
            boundaryTerm := by
    simpa [Ωnz, aggregateBudget, boundaryTerm] using
      hnboundary H hH Ω v hv
  rcases hres with hzero | hbudget
  · exact False.elim (ne_of_gt htermPos hzero)
  · exact hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_iff_residualBudget :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_positiveRatioResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_residualBudget⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_iff_residualBudget :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_positiveRatioResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_residualBudget⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_exactPolynomialBoundaryResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnone hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  simpa [Ωnz, actualBudget, exactBudget, oneTerm, hactualEq] using
    hnone H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudget_of_actualBoundaryResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnone hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  simpa [Ωnz, actualBudget, exactBudget, oneTerm, hactualEq] using
    hnone H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudget_iff_actualBoundaryResidualBudget :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_exactPolynomialBoundaryResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudget_of_actualBoundaryResidualBudget⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_exactPolynomialBoundaryResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnboundary hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  simpa [Ωnz, actualBudget, exactBudget, boundaryTerm, hactualEq] using
    hnboundary H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudget_of_actualBoundaryResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnboundary hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  simpa [Ωnz, actualBudget, exactBudget, boundaryTerm, hactualEq] using
    hnboundary H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudget_iff_actualBoundaryResidualBudget :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_exactPolynomialBoundaryResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudget_of_actualBoundaryResidualBudget⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_exactPolynomialBoundaryPositiveRatioResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnone hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  change 0 < oneTerm → actualBudget ≤ (D / 3) / oneTerm
  intro htermPos
  simpa [Ωnz, actualBudget, exactBudget, oneTerm, D, hactualEq] using
    hnone H hH Ω v hv htermPos

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudget_of_actualBoundaryPositiveRatioResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnone hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  change 0 < oneTerm → exactBudget ≤ (D / 3) / oneTerm
  intro htermPos
  simpa [Ωnz, actualBudget, exactBudget, oneTerm, D, hactualEq] using
    hnone H hH Ω v hv htermPos

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudget_iff_actualBoundaryPositiveRatioResidualBudget :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_exactPolynomialBoundaryPositiveRatioResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudget_of_actualBoundaryPositiveRatioResidualBudget⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_exactPolynomialBoundaryPositiveRatioResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnboundary hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  change 0 < boundaryTerm → actualBudget ≤ (D / 3) / boundaryTerm
  intro htermPos
  simpa [Ωnz, actualBudget, exactBudget, boundaryTerm, D, hactualEq] using
    hnboundary H hH Ω v hv htermPos

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudget_of_actualBoundaryPositiveRatioResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnboundary hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  change 0 < boundaryTerm → exactBudget ≤ (D / 3) / boundaryTerm
  intro htermPos
  simpa [Ωnz, actualBudget, exactBudget, boundaryTerm, D, hactualEq] using
    hnboundary H hH Ω v hv htermPos

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudget_iff_actualBoundaryPositiveRatioResidualBudget :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_exactPolynomialBoundaryPositiveRatioResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudget_of_actualBoundaryPositiveRatioResidualBudget⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointThirdBudgetSchedule
    {onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedulePositiveSubcritical
        onePointBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hnone H hH Ω v hv with ⟨hbudget, hpay⟩
  have htermNonneg : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) hβpos hH
  calc
    aggregateBudget * oneTerm ≤
        onePointBudget β H n Ωnz v * oneTerm :=
      mul_le_mul_of_nonneg_right hbudget htermNonneg
    _ ≤ D / 3 := by
      simpa [Ωnz, oneTerm, D] using hpay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairThirdBudgetSchedule
    {boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hnboundary H hH Ω v hv with ⟨hbudget, hpay⟩
  have htermNonneg : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) v hβpos hH
  calc
    aggregateBudget * boundaryTerm ≤
        boundaryPairBudget β H n Ωnz v * boundaryTerm :=
      mul_le_mul_of_nonneg_right hbudget htermNonneg
    _ ≤ D / 3 := by
      simpa [Ωnz, boundaryTerm, D] using hpay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_componentBudgetSchedules
    {onePointBudget boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedulePositiveSubcritical
        onePointBudget)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_components
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointThirdBudgetSchedule
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairThirdBudgetSchedule
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedule_of_domination_payment
    {onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hdom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetDominationSchedulePositiveSubcritical
        onePointBudget)
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedulePositiveSubcritical
        onePointBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedulePositiveSubcritical
      onePointBudget := by
  intro β hβpos hβc
  filter_upwards [hdom β hβpos hβc, hpay β hβpos hβc] with
    n hndom hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hdomLe :
      aggregateBudget ≤ onePointBudget β H n Ωnz v := by
    simpa [Ωnz, aggregateBudget] using hndom H hH Ω v hv
  have hpayLe :
      onePointBudget β H n Ωnz v * oneTerm ≤ D / 3 := by
    simpa [Ωnz, oneTerm, D] using hnpay H hH Ω v hv
  exact ⟨hdomLe, hpayLe⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedule_of_domination_payment
    {boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hdom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetDominationSchedulePositiveSubcritical
        boundaryPairBudget)
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedulePositiveSubcritical
      boundaryPairBudget := by
  intro β hβpos hβc
  filter_upwards [hdom β hβpos hβc, hpay β hβpos hβc] with
    n hndom hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hdomLe :
      aggregateBudget ≤ boundaryPairBudget β H n Ωnz v := by
    simpa [Ωnz, aggregateBudget] using hndom H hH Ω v hv
  have hpayLe :
      boundaryPairBudget β H n Ωnz v * boundaryTerm ≤ D / 3 := by
    simpa [Ωnz, boundaryTerm, D] using hnpay H hH Ω v hv
  exact ⟨hdomLe, hpayLe⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_componentBudgetDominationPayment
    {onePointBudget boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (honeDom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetDominationSchedulePositiveSubcritical
        onePointBudget)
    (honePay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedulePositiveSubcritical
        onePointBudget)
    (hboundaryDom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetDominationSchedulePositiveSubcritical
        boundaryPairBudget)
    (hboundaryPay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_componentBudgetSchedules
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedule_of_domination_payment
      honeDom honePay)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedule_of_domination_payment
      hboundaryDom hboundaryPay)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedule_of_positiveRatioPaymentSchedule
    {onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        onePointBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedulePositiveSubcritical
      onePointBudget := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change onePointBudget β H n Ωnz v * oneTerm ≤ D / 3
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  by_cases hzero : oneTerm = 0
  · have hDthird : 0 ≤ D / 3 := div_nonneg hD (by norm_num)
    simpa [hzero] using hDthird
  · have htermNonneg : 0 ≤ oneTerm := by
      simpa [oneTerm] using
        boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) hβpos hH
    have htermPos : 0 < oneTerm :=
      lt_of_le_of_ne htermNonneg (Ne.symm hzero)
    have hbudget :
        onePointBudget β H n Ωnz v ≤ (D / 3) / oneTerm := by
      simpa [Ωnz, oneTerm, D] using hnpay H hH Ω v hv htermPos
    calc
      onePointBudget β H n Ωnz v * oneTerm ≤
          ((D / 3) / oneTerm) * oneTerm :=
        mul_le_mul_of_nonneg_right hbudget htermNonneg
      _ = D / 3 := by
        rw [div_mul_cancel₀ _ hzero]

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedule_of_positiveRatioPaymentSchedule
    {boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedulePositiveSubcritical
      boundaryPairBudget := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change boundaryPairBudget β H n Ωnz v * boundaryTerm ≤ D / 3
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  by_cases hzero : boundaryTerm = 0
  · have hDthird : 0 ≤ D / 3 := div_nonneg hD (by norm_num)
    simpa [hzero] using hDthird
  · have htermNonneg : 0 ≤ boundaryTerm := by
      simpa [boundaryTerm] using
        boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) v hβpos hH
    have htermPos : 0 < boundaryTerm :=
      lt_of_le_of_ne htermNonneg (Ne.symm hzero)
    have hbudget :
        boundaryPairBudget β H n Ωnz v ≤ (D / 3) / boundaryTerm := by
      simpa [Ωnz, boundaryTerm, D] using
        hnpay H hH Ω v hv htermPos
    calc
      boundaryPairBudget β H n Ωnz v * boundaryTerm ≤
          ((D / 3) / boundaryTerm) * boundaryTerm :=
        mul_le_mul_of_nonneg_right hbudget htermNonneg
      _ = D / 3 := by
        rw [div_mul_cancel₀ _ hzero]

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedule_of_paymentSchedule
    {onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedulePositiveSubcritical
        onePointBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedulePositiveSubcritical
      onePointBudget := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change 0 < oneTerm →
    onePointBudget β H n Ωnz v ≤ (D / 3) / oneTerm
  intro htermPos
  have hmul :
      onePointBudget β H n Ωnz v * oneTerm ≤ D / 3 := by
    simpa [Ωnz, oneTerm, D] using hnpay H hH Ω v hv
  exact (le_div_iff₀ htermPos).2 hmul

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedule_of_paymentSchedule
    {boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedulePositiveSubcritical
      boundaryPairBudget := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change 0 < boundaryTerm →
    boundaryPairBudget β H n Ωnz v ≤ (D / 3) / boundaryTerm
  intro htermPos
  have hmul :
      boundaryPairBudget β H n Ωnz v * boundaryTerm ≤ D / 3 := by
    simpa [Ωnz, boundaryTerm, D] using hnpay H hH Ω v hv
  exact (le_div_iff₀ htermPos).2 hmul

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedule_iff_paymentSchedule
    {onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule} :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        onePointBudget ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedulePositiveSubcritical
        onePointBudget :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedule_of_positiveRatioPaymentSchedule,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedule_of_paymentSchedule⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedule_iff_paymentSchedule
    {boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule} :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        boundaryPairBudget ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedulePositiveSubcritical
        boundaryPairBudget :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedule_of_positiveRatioPaymentSchedule,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedule_of_paymentSchedule⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedule_of_domination_positiveRatioPayment
    {onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hdom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetDominationSchedulePositiveSubcritical
        onePointBudget)
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        onePointBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedulePositiveSubcritical
      onePointBudget :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedule_of_domination_payment
    hdom
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedule_of_positiveRatioPaymentSchedule
      hpay)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedule_of_domination_positiveRatioPayment
    {boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hdom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetDominationSchedulePositiveSubcritical
        boundaryPairBudget)
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedulePositiveSubcritical
      boundaryPairBudget :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedule_of_domination_payment
    hdom
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedule_of_positiveRatioPaymentSchedule
      hpay)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_componentBudgetDominationPositiveRatioPayment
    {onePointBudget boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (honeDom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetDominationSchedulePositiveSubcritical
        onePointBudget)
    (honePay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        onePointBudget)
    (hboundaryDom :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetDominationSchedulePositiveSubcritical
        boundaryPairBudget)
    (hboundaryPay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedulePositiveSubcritical
        boundaryPairBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_componentBudgetDominationPayment
    honeDom
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedule_of_positiveRatioPaymentSchedule
      honePay)
    hboundaryDom
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedule_of_positiveRatioPaymentSchedule
      hboundaryPay)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedule_of_cardSourceBoundaryEdgeBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        cardBudget sourceCardBudget edgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedulePositiveSubcritical
      (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
        cardBudget sourceCardBudget edgeMultiplicityBudget) := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hnone H hH Ω v hv with
    ⟨hcard, hsource, hsourceNonneg, hedge, hedgeNonneg, hpay⟩
  have hdomLe :
      aggregateBudget ≤
        boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
          cardBudget sourceCardBudget edgeMultiplicityBudget β H n Ωnz v := by
    simpa [
      aggregateBudget,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_le_cardSourceBoundaryEdgeBudget
        (n := n) Ωnz hcard hsource hsourceNonneg hedge hedgeNonneg
  have hpayLe :
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
          cardBudget sourceCardBudget edgeMultiplicityBudget β H n Ωnz v *
        oneTerm ≤ D / 3 := by
    simpa [
      Ωnz, oneTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule] using
      hpay
  exact ⟨hdomLe, hpayLe⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedule_of_cardSourceBoundaryEdgeBudgetSchedule
    {cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        cardBudget sourceCardBudget edgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedulePositiveSubcritical
      (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
        cardBudget sourceCardBudget edgeMultiplicityBudget) := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  rcases hnboundary H hH Ω v hv with
    ⟨hcard, hsource, hsourceNonneg, hedge, hedgeNonneg, hpay⟩
  have hdomLe :
      aggregateBudget ≤
        boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
          cardBudget sourceCardBudget edgeMultiplicityBudget β H n Ωnz v := by
    simpa [
      aggregateBudget,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_le_cardSourceBoundaryEdgeBudget
        (n := n) Ωnz hcard hsource hsourceNonneg hedge hedgeNonneg
  have hpayLe :
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
          cardBudget sourceCardBudget edgeMultiplicityBudget β H n Ωnz v *
        boundaryTerm ≤ D / 3 := by
    simpa [
      Ωnz, boundaryTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule] using
      hpay
  exact ⟨hdomLe, hpayLe⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_cardSourceBoundaryEdgeBudgetSchedules
    {oneCardBudget boundaryCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {oneSourceCardBudget boundarySourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {oneEdgeMultiplicityBudget boundaryEdgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        oneCardBudget oneSourceCardBudget oneEdgeMultiplicityBudget)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        boundaryCardBudget boundarySourceCardBudget
        boundaryEdgeMultiplicityBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_componentBudgetSchedules
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedule_of_cardSourceBoundaryEdgeBudgetSchedule
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedule_of_cardSourceBoundaryEdgeBudgetSchedule
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedule_of_actualSchedulePayment
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule]
  · simp [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule]
  · simpa [Ωnz,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  · simp [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule]
  · simpa [Ωnz,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ωnz,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  · simpa [Ωnz,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      hnpay H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedule_of_actualSchedulePayment
    (hpay :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule := by
  intro β hβpos hβc
  filter_upwards [hpay β hβpos hβc] with n hnpay
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule]
  · simp [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule]
  · simpa [Ωnz,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  · simp [
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule]
  · simpa [Ωnz,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ωnz,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  · simpa [Ωnz,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule] using
      hnpay H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_actualSchedulePayments
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_cardSourceBoundaryEdgeBudgetSchedules
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedule_of_actualSchedulePayment
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedule_of_actualSchedulePayment
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change aggregateBudget * oneTerm ≤ D / 3
  have hres :
      oneTerm = 0 ∨ aggregateBudget ≤ (D / 3) / oneTerm := by
    simpa [Ωnz, aggregateBudget, oneTerm, D] using hnone H hH Ω v hv
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  by_cases hzero : oneTerm = 0
  · have hDthird : 0 ≤ D / 3 := div_nonneg hD (by norm_num)
    simpa [hzero] using hDthird
  · have hbudget : aggregateBudget ≤ (D / 3) / oneTerm := by
      rcases hres with htermZero | hbudget
      · exact False.elim (hzero htermZero)
      · exact hbudget
    have htermNonneg : 0 ≤ oneTerm := by
      simpa [oneTerm] using
        boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) hβpos hH
    calc
      aggregateBudget * oneTerm ≤ ((D / 3) / oneTerm) * oneTerm :=
        mul_le_mul_of_nonneg_right hbudget htermNonneg
      _ = D / 3 := by
        rw [div_mul_cancel₀ _ hzero]

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change aggregateBudget * boundaryTerm ≤ D / 3
  have hres :
      boundaryTerm = 0 ∨ aggregateBudget ≤ (D / 3) / boundaryTerm := by
    simpa [Ωnz, aggregateBudget, boundaryTerm, D] using
      hnboundary H hH Ω v hv
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  by_cases hzero : boundaryTerm = 0
  · have hDthird : 0 ≤ D / 3 := div_nonneg hD (by norm_num)
    simpa [hzero] using hDthird
  · have hbudget : aggregateBudget ≤ (D / 3) / boundaryTerm := by
      rcases hres with htermZero | hbudget
      · exact False.elim (hzero htermZero)
      · exact hbudget
    have htermNonneg : 0 ≤ boundaryTerm := by
      simpa [boundaryTerm] using
        boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) v hβpos hH
    calc
      aggregateBudget * boundaryTerm ≤
          ((D / 3) / boundaryTerm) * boundaryTerm :=
        mul_le_mul_of_nonneg_right hbudget htermNonneg
      _ = D / 3 := by
        rw [div_mul_cancel₀ _ hzero]

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_residualBudgets
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_components
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointResidualBudget
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairResidualBudget
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointPositiveRatioResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointResidualBudget
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_positiveRatioResidualBudget
      hone)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairPositiveRatioResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairResidualBudget
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_positiveRatioResidualBudget
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_positiveRatioResidualBudgets
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_residualBudgets
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_positiveRatioResidualBudget
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_positiveRatioResidualBudget
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_exactPolynomialBoundaryPositiveRatioResidualBudgets
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_positiveRatioResidualBudgets
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_exactPolynomialBoundaryPositiveRatioResidualBudget
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_exactPolynomialBoundaryPositiveRatioResidualBudget
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_onePointThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change 0 < oneTerm → aggregateBudget ≤ (D / 3) / oneTerm
  intro htermPos
  have hthird : aggregateBudget * oneTerm ≤ D / 3 := by
    change aggregateBudget * oneTerm ≤ D / 3
    simpa [Ωnz, aggregateBudget, oneTerm, D] using hnone H hH Ω v hv
  exact (le_div_iff₀ htermPos).2 hthird

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_boundaryPairThird
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change 0 < boundaryTerm → aggregateBudget ≤ (D / 3) / boundaryTerm
  intro htermPos
  have hthird : aggregateBudget * boundaryTerm ≤ D / 3 := by
    change aggregateBudget * boundaryTerm ≤ D / 3
    simpa [Ωnz, aggregateBudget, boundaryTerm, D] using
      hnboundary H hH Ω v hv
  exact (le_div_iff₀ htermPos).2 hthird

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_iff_onePointThird :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointPositiveRatioResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget_of_onePointThird⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_iff_boundaryPairThird :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairPositiveRatioResidualBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget_of_boundaryPairThird⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_aggregateEnvelopeActualBoundaryOnePointThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcapLe : cap ≤ aggregateBudget := by
    simpa [cap, aggregateBudget] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_aggregateActualBoundaryBudget
        β H Ωnz
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) hβpos hH
  have hbudget : aggregateBudget * oneTerm ≤ D / 3 := by
    change aggregateBudget * oneTerm ≤ D / 3
    simpa [Ωnz, aggregateBudget, oneTerm, D] using hnone H hH Ω v hv
  calc
    cap * oneTerm ≤ aggregateBudget * oneTerm :=
      mul_le_mul_of_nonneg_right hcapLe honeTerm
    _ ≤ D / 3 := hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_aggregateEnvelopeActualBoundaryBoundaryPairThird
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz
  let aggregateBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcapLe : cap ≤ aggregateBudget := by
    simpa [cap, aggregateBudget] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_aggregateActualBoundaryBudget
        β H Ωnz
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) v hβpos hH
  have hbudget : aggregateBudget * boundaryTerm ≤ D / 3 := by
    change aggregateBudget * boundaryTerm ≤ D / 3
    simpa [Ωnz, aggregateBudget, boundaryTerm, D] using
      hnboundary H hH Ω v hv
  calc
    cap * boundaryTerm ≤ aggregateBudget * boundaryTerm :=
      mul_le_mul_of_nonneg_right hcapLe hboundaryTerm
    _ ≤ D / 3 := hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_aggregateEnvelopeActualBoundaryOnePointResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_aggregateEnvelopeActualBoundaryOnePointThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_onePointResidualBudget
      hone)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_aggregateEnvelopeActualBoundaryBoundaryPairResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_aggregateEnvelopeActualBoundaryBoundaryPairThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_boundaryPairResidualBudget
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_aggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudget
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_aggregateEnvelopeActualBoundaryOnePointResidualBudget
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudget_of_positiveRatioResidualBudget
      hone)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_aggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudget
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_aggregateEnvelopeActualBoundaryBoundaryPairResidualBudget
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudget_of_positiveRatioResidualBudget
      hboundary)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_aggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz
  let cardBudget := (Ωnz.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ωnz,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  let multiplicityBudget := boundaryCard * edgeBudget
  let summandBudget :=
    sourceCardBudget * multiplicityBudget * multiplicityBudget
  let aggregateBudget := cardBudget * summandBudget
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let emptyTerm :=
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hsourceBudgetNonneg : 0 ≤ sourceCardBudget := by
    simpa [sourceCardBudget] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  have hedgeBudgetNonneg : 0 ≤ edgeBudget := by
    simpa [edgeBudget] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ωnz,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  have hboundaryCardNonneg : 0 ≤ boundaryCard := by
    simp [boundaryCard]
  have hmultiplicityBudgetNonneg : 0 ≤ multiplicityBudget :=
    mul_nonneg hboundaryCardNonneg hedgeBudgetNonneg
  have hsummand :
      ∀ m, m ∈ Ωnz →
        ((finiteBoundaryGhostSourceSector m).card : ℝ) *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
          summandBudget := by
    intro m hm
    have hsource :
        ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
          sourceCardBudget := by
      simpa [sourceCardBudget] using
        finiteBoundaryGhostSourceSector_card_le_cutoff_sourceSector_card_sum
          (n := n) (Ω := Ωnz) (m := m) hm
    have hedge :
        ∀ w, w ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
            edgeBudget := by
      intro w hw
      simpa [edgeBudget] using
        finiteBoundaryGhostBoundaryEdgeMultiplicity_le_cutoff_boundaryEdge_sum
          (n := n) (Ω := Ωnz) (m := m) hm (w := w) hw
    have hmult :
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
          multiplicityBudget := by
      have hsum :=
        finiteBoundaryGhostBoundaryGhostMultiplicitySum_le_boundaryCard_mul_of_edgeMultiplicity_le
          (n := n) m hedge
      simpa [boundaryCard, multiplicityBudget] using hsum
    simpa [summandBudget] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_le_sourceCard_mul_multiplicityBudget_sq
        (n := n) m hsource hmult hsourceBudgetNonneg
        hmultiplicityBudgetNonneg
  have hcapLe : cap ≤ aggregateBudget := by
    have hcard :=
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_card_mul_of_summand_le
        (β := β) (H := H) (Ω := Ωnz) hsummand
    simpa [cap, cardBudget, summandBudget, aggregateBudget] using hcard
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have hcombinedNonneg : 0 ≤ oneTerm + boundaryTerm :=
    add_nonneg honeTerm hboundaryTerm
  have hmul :
      cap * (oneTerm + boundaryTerm) ≤
        aggregateBudget * (oneTerm + boundaryTerm) :=
    mul_le_mul_of_nonneg_right hcapLe hcombinedNonneg
  have hbudget :
      aggregateBudget * (oneTerm + boundaryTerm) + emptyTerm ≤ D := by
    have hbudgetRaw := hn H hH Ω v hv
    exact hbudgetRaw
  calc
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz *
            boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
          boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz *
            boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v +
        boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v =
        cap * (oneTerm + boundaryTerm) + emptyTerm := by
      ring
    _ ≤ aggregateBudget * (oneTerm + boundaryTerm) + emptyTerm :=
      add_le_add hmul le_rfl
    _ ≤ D := hbudget

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCap_le_residual_div_combined_of_componentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
      ∀ᶠ n in atTop,
        ∀ H : ℝ, 0 < H →
          ∀ Ω : Finset
            (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              0 <
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v →
                boundaryCrossingCapSourceSectorMultiplicitySquareBound
                    β H n Ω ≤
                  (boundaryVertexBoxSimonCurrentRatio β n v -
                      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                        β H n v) /
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv hcombined
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let combined :=
    boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let emptyTerm :=
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcombined' : 0 < combined := by
    simpa [combined] using hcombined
  have hsum : cap * combined + emptyTerm ≤ D := by
    simpa [cap, combined, emptyTerm, D] using hn H hH Ω v hv
  have hmul : cap * combined ≤ D - emptyTerm := by
    linarith
  calc
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω = cap := by
      rfl
    _ = (cap * combined) / combined := by
      field_simp [hcombined'.ne']
    _ ≤ (D - emptyTerm) / combined :=
      div_le_div_of_nonneg_right hmul (le_of_lt hcombined')

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummandSum_le_residual_div_combined_of_componentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
      ∀ᶠ n in atTop,
        ∀ H : ℝ, 0 < H →
          ∀ Γ : Finset
            (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              0 <
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v →
                (∑ m ∈ Γ,
                  ((finiteBoundaryGhostSourceSector m).card : ℝ) *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m) ≤
                  (boundaryVertexBoxSimonCurrentRatio β n v -
                      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                        β H n v) /
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) := by
  intro β hβpos hβc
  filter_upwards [
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCap_le_residual_div_combined_of_componentSumUncutoffCombined
      h β hβpos hβc] with n hn
  intro H hH Γ v hv hcombined
  have hcap := hn H hH Γ v hv hcombined
  simpa [boundaryCrossingCapSourceSectorMultiplicitySquareBound] using hcap

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCard_mul_lowerBound_le_residual_div_combined_of_componentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
      ∀ᶠ n in atTop,
        ∀ H : ℝ, 0 < H →
          ∀ Γ : Finset
            (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
            ∀ δ : ℝ,
              (∀ m, m ∈ Γ →
                δ ≤
                  ((finiteBoundaryGhostSourceSector m).card : ℝ) *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m) →
              ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
                0 <
                    boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                      β H n v →
                  ((Γ.card : ℝ) * δ) ≤
                    (boundaryVertexBoxSimonCurrentRatio β n v -
                        boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                          β H n v) /
                      (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                        boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                          β H n v) := by
  intro β hβpos hβc
  filter_upwards [
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummandSum_le_residual_div_combined_of_componentSumUncutoffCombined
      h β hβpos hβc] with n hn
  intro H hH Γ δ hδ v hv hcombined
  have hsumBound := hn H hH Γ v hv hcombined
  have hcardBound :
      ((Γ.card : ℝ) * δ) ≤
        ∑ m ∈ Γ,
          ((finiteBoundaryGhostSourceSector m).card : ℝ) *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
    have hsum :
        (∑ m ∈ Γ, δ) ≤
          ∑ m ∈ Γ,
            ((finiteBoundaryGhostSourceSector m).card : ℝ) *
              finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
              finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
      exact Finset.sum_le_sum (fun m hm => hδ m hm)
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  exact le_trans hcardBound hsumBound

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummand_le_residual_div_combined_of_componentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
      ∀ᶠ n in atTop,
        ∀ H : ℝ, 0 < H →
          ∀ m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
            ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
              0 <
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v →
                ((finiteBoundaryGhostSourceSector m).card : ℝ) *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
                  (boundaryVertexBoxSimonCurrentRatio β n v -
                      boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                        β H n v) /
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) := by
  intro β hβpos hβc
  filter_upwards [
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCap_le_residual_div_combined_of_componentSumUncutoffCombined
      h β hβpos hβc] with n hn
  intro H hH m v hv hcombined
  have hsingle :=
    hn H hH
      ({m} : Finset
        (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
      v hv hcombined
  simpa [
    boundaryCrossingCapSourceSectorMultiplicitySquareBound_singleton] using
    hsingle

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_combinedTwoThird_emptyThird
    (hcombined :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOneBoundaryCombinedTwoThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcombined β hβpos hβc, hempty β hβpos hβc] with
    n hncombined hnempty
  intro H hH Ω v hv
  let cap := boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcombinedLe :
      cap * (oneTerm + boundaryTerm) ≤ 2 * D / 3 := by
    simpa [cap, oneTerm, boundaryTerm, D] using
      hncombined H hH Ω v hv
  have hemptyLe : emptyTerm ≤ D / 3 := by
    simpa [emptyTerm, D] using hnempty H hH Ω v hv
  calc
    cap * (oneTerm + boundaryTerm) + emptyTerm ≤ 2 * D / 3 + D / 3 :=
      add_le_add hcombinedLe hemptyLe
    _ = D := by
      ring

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_components
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_combinedTwoThird_emptyThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOneBoundaryCombinedTwoThirdUncutoff_of_components
      hone hboundary)
    hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let capSmall :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz
  let capLarge :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcapLe : capSmall ≤ capLarge := by
    simpa [capSmall, capLarge, Ωnz] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_weightNonzeroCutoff_le
        β H Ω
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have hcombinedTerm : 0 ≤ oneTerm + boundaryTerm :=
    add_nonneg honeTerm hboundaryTerm
  have hcapMul :
      capSmall * (oneTerm + boundaryTerm) ≤
        capLarge * (oneTerm + boundaryTerm) :=
    mul_le_mul_of_nonneg_right hcapLe hcombinedTerm
  have huncut :
      capLarge * (oneTerm + boundaryTerm) + emptyTerm ≤ D := by
    simpa [capLarge, oneTerm, boundaryTerm, emptyTerm, D] using
      hn H hH Ω v hv
  calc
    capSmall * oneTerm + capSmall * boundaryTerm + emptyTerm =
        capSmall * (oneTerm + boundaryTerm) + emptyTerm := by
      ring
    _ ≤ capLarge * (oneTerm + boundaryTerm) + emptyTerm :=
      add_le_add hcapMul (le_refl emptyTerm)
    _ ≤ D := huncut

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_combinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_combinedEmptyShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_componentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_componentShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_capBudgetUncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetUncutoff
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_capBudgetScheduleUncutoff
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetScheduleUncutoff
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_components
      hone hboundary hempty)

end Exact3D
end StatMech
