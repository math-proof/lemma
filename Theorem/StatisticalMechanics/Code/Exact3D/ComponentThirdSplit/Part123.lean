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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part133
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfile_of_unpaidRemainderPlusCollapsedActiveImageLeProfile
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let active :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
      β H n Ωnz v
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let collapsedActive :=
    ∑ d ∈ I.image,
      (((I.fiber d).card : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hcollapsed :
      R + collapsedActive ≤ profile := by
    simpa [Ωnz, cap, D, paid, R, profile, I, collapsedActive] using
      hn H hH Ω v hv
  have hactive_eq : active = collapsedActive := by
    simpa [active, I, collapsedActive] using
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_eq_collapsedVertexCutoffDecrementIndex_image_sum
        β H n Ωnz v
  have hprofile : R + active ≤ profile := by
    simpa [hactive_eq] using hcollapsed
  simpa [Ωnz, cap, D, paid, R, profile, active] using hprofile

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfile_of_unpaidRemainderPlusActiveLeProfile
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let active :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
      β H n Ωnz v
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let collapsedActive :=
    ∑ d ∈ I.image,
      (((I.fiber d).card : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hactive :
      R + active ≤ profile := by
    simpa [Ωnz, cap, D, paid, R, profile, active] using
      hn H hH Ω v hv
  have hactive_eq : active = collapsedActive := by
    simpa [active, I, collapsedActive] using
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_eq_collapsedVertexCutoffDecrementIndex_image_sum
        β H n Ωnz v
  have hcollapsed : R + collapsedActive ≤ profile := by
    simpa [hactive_eq] using hactive
  simpa [Ωnz, cap, D, paid, R, profile, I, collapsedActive] using hcollapsed

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfile_iff_unpaidRemainderPlusCollapsedActiveImageLeProfile :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfile_of_unpaidRemainderPlusActiveLeProfile,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfile_of_unpaidRemainderPlusCollapsedActiveImageLeProfile⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderLeCollapsedMainEmptyGap
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  have hgap :
      R ≤ mainGap + (emptyBudget - restoredCopy) := by
    simpa [Ωnz, cap, D, paid, R, I, mainTerm, boundaryMultiplicity,
      restoredCopy, mainGap, emptyBudget] using hn H hH Ω v hv
  have hmainGap : mainGap = mainBudget - boundaryMultiplicity := by
    dsimp [mainGap, mainBudget, boundaryMultiplicity]
    calc
        (∑ d ∈ I.image,
            (mainTerm -
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                ℕ) : ℝ) *
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        (∑ _d ∈ I.image, mainTerm) -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_sub_distrib]
      _ =
        (I.image.card : ℝ) * mainTerm -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
    linarith
  simpa [Ωnz, cap, D, paid, R, I, mainTerm, boundaryMultiplicity,
    restoredCopy, mainBudget, emptyBudget] using htotal

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap :=
    ∑ d ∈ I.image,
      (mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
    simpa [Ωnz, cap, D, paid, R, I, mainTerm, boundaryMultiplicity,
      restoredCopy, mainBudget, emptyBudget] using hn H hH Ω v hv
  have hmainGap : mainGap = mainBudget - boundaryMultiplicity := by
    dsimp [mainGap, mainBudget, boundaryMultiplicity]
    calc
        (∑ d ∈ I.image,
            (mainTerm -
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                ℕ) : ℝ) *
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        (∑ _d ∈ I.image, mainTerm) -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_sub_distrib]
      _ =
        (I.image.card : ℝ) * mainTerm -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hgap :
      R ≤ mainGap + (emptyBudget - restoredCopy) := by
    linarith
  simpa [Ωnz, cap, D, paid, R, I, mainTerm, mainGap, emptyBudget,
    restoredCopy] using hgap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderLeCollapsedMainEmptyGap⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_mainGap_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (d : finiteBoundaryGhostCollapsedTwoPointSourceData n v) :
    0 ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hle :
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_weight_le_boundaryFiberSourcePairVertexMainTerm
      (β := β) (H := H) hβ hH hvbdry d
  linarith

set_option linter.style.longLine false in


theorem finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
        (∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
  have hle :
      (∑ d ∈ (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v :=
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_weight_sum_le_boundaryFiberSourcePairVertexEmptyTerm
      (β := β) (H := H) hβ hH Ω v
  linarith

set_option linter.style.longLine false in

theorem finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
    0 ≤
      ∑ d ∈ I.image,
        (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) := by
  classical
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
  change
    0 ≤
      ∑ d ∈ I.image,
        (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  refine Finset.sum_nonneg ?_
  intro d _hd
  exact
    finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_mainGap_nonneg
      (β := β) (H := H) hβ hH hv d

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ candidateSlots : Atom → Finset Slot,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ S : Finset Atom, S ⊆ atoms →
                  S.card ≤
                    (@Finset.biUnion Atom Slot (Classical.decEq Slot)
                      S candidateSlots).card) ∧
                  (∀ a, a ∈ atoms → ∀ slot, slot ∈ candidateSlots a →
                    match slot with
                    | Sum.inl d => d ∈ I.image ∧ demand a ≤ mainGap d
                    | Sum.inr _ => demand a ≤ emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hHall⟩
  let candidateSlots : Atom → Finset Slot :=
    canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
  refine
    ⟨Atom, atoms, demand, candidateSlots, hdemandNonneg, hRle, ?_, ?_⟩
  · simpa [candidateSlots] using hHall
  · intro a _ha slot hslot
    have hslot' :
        slot ∈
          canonicalCapacityCandidateSlots I.image mainGap emptyGap demand a := by
      simpa [candidateSlots] using hslot
    cases slot with
    | inl d =>
        exact
          canonicalCapacityCandidateSlots_mem_compatible
            (mainSlots := I.image) (mainCap := mainGap)
            (emptyCap := emptyGap) (demand := demand) (a := a)
            (slot := Sum.inl d) hslot'
    | inr u =>
        exact
          canonicalCapacityCandidateSlots_mem_compatible
            (mainSlots := I.image) (mainCap := mainGap)
            (emptyCap := emptyGap) (demand := demand) (a := a)
            (slot := Sum.inr u) hslot'

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ a, a ∈ atoms →
                ∃ route :
                  {b // b ∈ atoms ∧ demand a ≤ demand b} → Slot,
                  (∀ b,
                    match route b with
                    | Sum.inl d => d ∈ I.image ∧ demand a ≤ mainGap d
                    | Sum.inr _ => demand a ≤ emptyGap) ∧
                    Function.Injective route)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThresholdEmbedding⟩
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  intro a ha
  rcases hThresholdEmbedding a ha with ⟨route⟩
  refine ⟨fun b => (route b).1, ?_, ?_⟩
  · intro b
    cases hslot : (route b).1 with
    | inl d =>
        have hmem :
            Sum.inl d ∈
              canonicalCapacityCandidateSlots
                I.image mainGap emptyGap demand a := by
          simpa [hslot] using (route b).2
        simpa [hslot] using
          (canonicalCapacityCandidateSlots_mem_compatible
            (mainSlots := I.image) (mainCap := mainGap)
            (emptyCap := emptyGap) (demand := demand) (a := a)
            (slot := Sum.inl d) hmem)
    | inr u =>
        have hmem :
            Sum.inr u ∈
              canonicalCapacityCandidateSlots
                I.image mainGap emptyGap demand a := by
          simpa [hslot] using (route b).2
        simpa [hslot] using
          (canonicalCapacityCandidateSlots_mem_compatible
            (mainSlots := I.image) (mainCap := mainGap)
            (emptyCap := emptyGap) (demand := demand) (a := a)
            (slot := Sum.inr u) hmem)
  · intro b c hbc
    apply route.injective
    exact Subtype.ext hbc

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical := by
  classical
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ a, a ∈ atoms →
                ∃ route : Atom → Slot,
                  (∀ b, b ∈ atoms → demand a ≤ demand b →
                    match route b with
                    | Sum.inl d => d ∈ I.image ∧ demand a ≤ mainGap d
                    | Sum.inr _ => demand a ≤ emptyGap) ∧
                    Set.InjOn route
                      (atoms.filter (fun b => demand a ≤ demand b) :
                        Set Atom))
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThresholdSubtype⟩
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  intro a ha
  rcases hThresholdSubtype a ha with ⟨route, hroute, hinj⟩
  let route' : Atom → Slot :=
    fun b =>
      if hb : b ∈ atoms ∧ demand a ≤ demand b then
        route ⟨b, hb⟩
      else
        Sum.inr ()
  refine ⟨route', ?_, ?_⟩
  · intro b hb hle
    have hbsub : b ∈ atoms ∧ demand a ≤ demand b := ⟨hb, hle⟩
    simpa [route', hbsub, I, mainGap, emptyGap] using hroute ⟨b, hbsub⟩
  · intro b hb c hc hbc
    have hb' := Finset.mem_filter.mp hb
    have hc' := Finset.mem_filter.mp hc
    have hbsub : b ∈ atoms ∧ demand a ≤ demand b := hb'
    have hcsub : c ∈ atoms ∧ demand a ≤ demand c := hc'
    have hrouteEq : route ⟨b, hbsub⟩ = route ⟨c, hcsub⟩ := by
      simpa [route', hbsub, hcsub] using hbc
    exact congrArg Subtype.val (hinj hrouteEq)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ a, a ∈ atoms →
                (atoms.filter (fun b => demand a ≤ demand b)).card ≤
                  (I.image.filter (fun d => demand a ≤ mainGap d)).card +
                    if demand a ≤ emptyGap then 1 else 0)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThresholdInj⟩
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  intro a ha
  rcases hThresholdInj a ha with ⟨route, hroute, hinj⟩
  let route' : Atom → Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit :=
    route
  have hroute' :
      ∀ b, b ∈ atoms → demand a ≤ demand b →
        match route' b with
        | Sum.inl d => d ∈ I.image ∧ demand a ≤ mainGap d
        | Sum.inr _ => demand a ≤ emptyGap := by
    intro b hb hle
    simpa [route', I, mainGap, emptyGap] using hroute b hb hle
  have hinj' :
      Set.InjOn route'
        (atoms.filter (fun b => demand a ≤ demand b) : Set Atom) := by
    simpa [route'] using hinj
  have hmaps :
      Set.MapsTo route'
        (atoms.filter (fun b => demand a ≤ demand b) : Set Atom)
        (canonicalCapacityCandidateSlots
          I.image mainGap emptyGap demand a :
            Set (Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit)) := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hcompat := hroute' b hb'.1 hb'.2
    cases hslot : route' b with
    | inl d =>
        rw [hslot] at hcompat
        simp [canonicalCapacityCandidateSlots, hcompat]
    | inr u =>
        rw [hslot] at hcompat
        simp [canonicalCapacityCandidateSlots, hcompat]
  have hle :
      (atoms.filter (fun b => demand a ≤ demand b)).card ≤
        (canonicalCapacityCandidateSlots I.image mainGap emptyGap demand a).card :=
    Finset.card_le_card_of_injOn route' hmaps hinj'
  have hcard :
      (canonicalCapacityCandidateSlots I.image mainGap emptyGap demand a).card =
        (I.image.filter (fun d => demand a ≤ mainGap d)).card +
          if demand a ≤ emptyGap then 1 else 0 :=
    canonicalCapacityCandidateSlots_card
      (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand) (a := a)
  exact le_trans hle (le_of_eq hcard)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          let candidateSlots : Atom → Finset Slot :=
            canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ a, a ∈ atoms →
                (atoms.filter (fun b => demand a ≤ demand b)).card ≤
                  (candidateSlots a).card)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThreshold⟩
  let candidateSlots : Atom → Finset Slot :=
    canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  intro a ha
  have hcard :
      (candidateSlots a).card =
        (I.image.filter (fun d => demand a ≤ mainGap d)).card +
          if demand a ≤ emptyGap then 1 else 0 := by
    simpa [candidateSlots] using
      (canonicalCapacityCandidateSlots_card
        (mainSlots := I.image) (mainCap := mainGap)
        (emptyCap := emptyGap) (demand := demand) (a := a))
  rw [hcard]
  exact hThreshold a ha

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          let candidateSlots : Atom → Finset Slot :=
            canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ S : Finset Atom, S ⊆ atoms →
                S.card ≤
                  (@Finset.biUnion Atom Slot (Classical.decEq Slot)
                    S candidateSlots).card)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThreshold⟩
  let candidateSlots : Atom → Finset Slot :=
    canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  intro S hS
  have hHall :
      S.card ≤
        (@Finset.biUnion Atom Slot (Classical.decEq Slot)
          S
          (canonicalCapacityCandidateSlots
            I.image mainGap emptyGap demand)).card :=
    finiteHallCondition_of_capacityThresholdCounts
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand)
      (hThreshold := by
        intro a ha
        simpa [candidateSlots] using hThreshold a ha)
      S hS
  simpa [candidateSlots] using hHall

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ a, a ∈ atoms →
                (atoms.filter (fun b => demand a ≤ demand b)).card ≤
                  (I.image.filter (fun d => demand a ≤ mainGap d)).card +
                    if demand a ≤ emptyGap then 1 else 0)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hHall⟩
  let candidateSlots : Atom → Finset Slot :=
    canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
  have hHall' :
      ∀ S : Finset Atom, S ⊆ atoms →
        S.card ≤
          (@Finset.biUnion Atom Slot (Classical.decEq Slot)
            S
            (canonicalCapacityCandidateSlots
              I.image mainGap emptyGap demand)).card := by
    intro S hS
    simpa [candidateSlots] using hHall S hS
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  exact
    (finiteHallCondition_capacityThresholdScalarCounts_iff
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand)).mp hHall'

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          let candidateSlots : Atom → Finset Slot :=
            canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
            R ≤ ∑ a ∈ atoms, demand a ∧
              (∀ S : Finset Atom, S ⊆ atoms →
                S.card ≤
                  (@Finset.biUnion Atom Slot (Classical.decEq Slot)
                    S candidateSlots).card)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hne, hdisj⟩
  let candidateSlots : Atom → Finset Slot :=
    canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  exact
    finiteHallCondition_of_pairwiseDisjoint_nonempty
      (atoms := atoms) (candidateSlots := candidateSlots)
      (hne := by
        intro a ha
        simpa [candidateSlots] using hne a ha)
      (hdisj := by
        intro a ha b hb hab
        simpa [candidateSlots] using hdisj a ha b hb hab)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ route :
              Atom →
                Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ a, a ∈ atoms →
                  match route a with
                  | Sum.inl d => d ∈ I.image
                  | Sum.inr _ => True) ∧
                  Set.InjOn route atoms ∧
                    (∀ a, a ∈ atoms →
                      demand a ≤
                        match route a with
                        | Sum.inl d => mainGap d
                        | Sum.inr _ => emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hne, hdisj⟩
  let candidateSlots : Atom → Finset Slot :=
    canonicalCapacityCandidateSlots I.image mainGap emptyGap demand
  have hneScalar :
      ∀ a, a ∈ atoms →
        (∃ d, d ∈ I.image ∧ demand a ≤ mainGap d) ∨
          demand a ≤ emptyGap := by
    intro a ha
    have hne' :
        (canonicalCapacityCandidateSlots
          I.image mainGap emptyGap demand a).Nonempty := by
      simpa [candidateSlots] using hne a ha
    exact
      (canonicalCapacityCandidateSlots_nonempty_iff
        (mainSlots := I.image) (mainCap := mainGap)
        (emptyCap := emptyGap) (demand := demand) (a := a)).mp hne'
  have hdisjScalarMax :
      ∀ a, a ∈ atoms → ∀ b, b ∈ atoms → a ≠ b →
        (∀ d, d ∈ I.image →
          mainGap d < max (demand a) (demand b)) ∧
          emptyGap < max (demand a) (demand b) := by
    intro a ha b hb hab
    have hdisj' :
        Disjoint
          (canonicalCapacityCandidateSlots I.image mainGap emptyGap demand a)
          (canonicalCapacityCandidateSlots I.image mainGap emptyGap demand b) := by
      simpa [candidateSlots] using hdisj a ha b hb hab
    exact
      (canonicalCapacityCandidateSlots_disjoint_iff_capacity_lt_max
        (mainSlots := I.image) (mainCap := mainGap)
        (emptyCap := emptyGap) (demand := demand) a b).mp hdisj'
  rcases
    canonicalCapacityGlobalRouteInjOn_of_capacityScalarMaxDisjoint_nonempty
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand) hneScalar hdisjScalarMax with
    ⟨route, hroute, hinj⟩
  refine ⟨Atom, atoms, demand, route, hdemandNonneg, hRle, ?_, hinj, ?_⟩
  · intro a ha
    have hroute' := hroute a ha
    cases hslot : route a with
    | inl d =>
        have hmain : d ∈ I.image ∧ demand a ≤ mainGap d := by
          simpa [hslot] using hroute'
        exact hmain.1
    | inr u =>
        trivial
  · intro a ha
    have hroute' := hroute a ha
    cases hslot : route a with
    | inl d =>
        have hmain : d ∈ I.image ∧ demand a ≤ mainGap d := by
          simpa [hslot] using hroute'
        exact hmain.2
    | inr u =>
        simpa [hslot] using hroute'

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ route :
              Atom →
                Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ a, a ∈ atoms →
                  match route a with
                  | Sum.inl d => d ∈ I.image
                  | Sum.inr _ => True) ∧
                  Set.InjOn route atoms ∧
                    (∀ a, a ∈ atoms →
                      demand a ≤
                        match route a with
                        | Sum.inl d => mainGap d
                        | Sum.inr _ => emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, subtypeRoute, hdemandNonneg, hRle, hrouteMem,
      hrouteInjective, hroutePays⟩
  classical
  let defaultSlot :
      Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit :=
    Sum.inr ()
  let route :
      Atom → Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit :=
    fun a => if ha : a ∈ atoms then subtypeRoute ⟨a, ha⟩ else defaultSlot
  refine ⟨Atom, atoms, demand, route, hdemandNonneg, hRle, ?_, ?_, ?_⟩
  · intro a ha
    have hmem := hrouteMem ⟨a, ha⟩
    simpa [route, ha] using hmem
  · intro a ha b hb hrouteEq
    have hsubRoute :
        subtypeRoute ⟨a, ha⟩ = subtypeRoute ⟨b, hb⟩ := by
      have hrouteA : route a = subtypeRoute ⟨a, ha⟩ := by
        change
          (if hmem : a ∈ atoms then subtypeRoute ⟨a, hmem⟩ else
            defaultSlot) =
            subtypeRoute ⟨a, ha⟩
        exact dif_pos ha
      have hrouteB : route b = subtypeRoute ⟨b, hb⟩ := by
        change
          (if hmem : b ∈ atoms then subtypeRoute ⟨b, hmem⟩ else
            defaultSlot) =
            subtypeRoute ⟨b, hb⟩
        exact dif_pos hb
      calc
        subtypeRoute ⟨a, ha⟩ = route a := hrouteA.symm
        _ = route b := hrouteEq
        _ = subtypeRoute ⟨b, hb⟩ := hrouteB
    exact congrArg Subtype.val (hrouteInjective hsubRoute)
  · intro a ha
    have hpays := hroutePays ⟨a, ha⟩
    simpa [route, ha] using hpays

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionCharge_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ route :
              {a // a ∈ atoms} →
                Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ a : {a // a ∈ atoms},
                  match route a with
                  | Sum.inl d => d ∈ I.image
                  | Sum.inr _ => True) ∧
                  Function.Injective route ∧
                    (∀ a : {a // a ∈ atoms},
                      demand a.1 ≤
                        match route a with
                        | Sum.inl d => mainGap d
                        | Sum.inr _ => emptyGap)
  intro _hnonpos _hmainShortcut _hemptyShortcut
  rcases hn H hH Ω v hv with
    ⟨mainShare, emptyShare, hmainShareNonneg, hemptyShareNonneg, hRle,
      hmainShareLe, hemptyShareLe⟩
  classical
  let Slot := Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
  let atoms : Finset Slot :=
    (I.image.image
        (Sum.inl :
          finiteBoundaryGhostCollapsedTwoPointSourceData n v → Slot)) ∪
      ({Sum.inr ()} : Finset Slot)
  let demand : Slot → ℝ :=
    fun slot =>
      match slot with
      | Sum.inl d => mainShare d
      | Sum.inr _ => emptyShare
  let route : {a // a ∈ atoms} → Slot := fun a => a.1
  refine ⟨Slot, atoms, demand, route, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    cases a with
    | inl d =>
        have hd : d ∈ I.image := by
          have hmemUnion :
              (Sum.inl d : Slot) ∈
                (I.image.image
                    (Sum.inl :
                      finiteBoundaryGhostCollapsedTwoPointSourceData n v →
                        Slot)) ∪
                  ({Sum.inr ()} : Finset Slot) := by
            simpa only [atoms] using ha
          rcases Finset.mem_union.mp hmemUnion with hmain | hempty
          · rcases Finset.mem_image.mp hmain with ⟨d', hd', hd'eq⟩
            exact (Sum.inl.inj hd'eq).symm ▸ hd'
          · exact False.elim (Sum.inl_ne_inr (Finset.mem_singleton.mp hempty))
        simpa [demand] using hmainShareNonneg d hd
    | inr u =>
        simpa [demand] using hemptyShareNonneg
  · have hsum :
        (∑ a ∈ atoms, demand a) =
          (∑ d ∈ I.image, mainShare d) + emptyShare := by
      let mainAtoms : Finset Slot :=
        I.image.image
          (Sum.inl :
            finiteBoundaryGhostCollapsedTwoPointSourceData n v → Slot)
      let emptyAtoms : Finset Slot := {Sum.inr ()}
      have hdisjoint : Disjoint mainAtoms emptyAtoms := by
        rw [Finset.disjoint_left]
        intro x hx hsingle
        rcases Finset.mem_image.mp hx with ⟨d, _hd, rfl⟩
        exact Sum.inl_ne_inr (Finset.mem_singleton.mp hsingle)
      have hmain :
          (∑ a ∈ mainAtoms, demand a) =
            ∑ d ∈ I.image, mainShare d := by
        simpa [mainAtoms, demand] using
          (Finset.sum_image
            (s := I.image)
            (g := (Sum.inl :
              finiteBoundaryGhostCollapsedTwoPointSourceData n v → Slot))
            (f := demand)
            (by
              intro d _hd e _he hde
              exact Sum.inl.inj hde))
      calc
        (∑ a ∈ atoms, demand a) =
            (∑ a ∈ mainAtoms, demand a) +
              ∑ a ∈ emptyAtoms, demand a := by
              simpa [atoms, mainAtoms, emptyAtoms] using
                (Finset.sum_union hdisjoint (f := demand))
        _ = (∑ d ∈ I.image, mainShare d) + emptyShare := by
              simp [hmain, emptyAtoms, demand]
    rw [hsum]
    exact hRle
  · intro a
    cases hslot : route a with
    | inl d =>
        have hmem : (Sum.inl d : Slot) ∈ atoms := by
          simpa [route, hslot] using a.2
        have hd : d ∈ I.image := by
          have hmemUnion :
              (Sum.inl d : Slot) ∈
                (I.image.image
                    (Sum.inl :
                      finiteBoundaryGhostCollapsedTwoPointSourceData n v →
                        Slot)) ∪
                  ({Sum.inr ()} : Finset Slot) := by
            simpa only [atoms] using hmem
          rcases Finset.mem_union.mp hmemUnion with hmain | hempty
          · rcases Finset.mem_image.mp hmain with ⟨d', hd', hd'eq⟩
            exact (Sum.inl.inj hd'eq).symm ▸ hd'
          · exact False.elim (Sum.inl_ne_inr (Finset.mem_singleton.mp hempty))
        simpa [route, hslot] using hd
    | inr u =>
        trivial
  · intro a b hab
    exact Subtype.ext hab
  · intro a
    cases hslot : route a with
    | inl d =>
        have hmem : (Sum.inl d : Slot) ∈ atoms := by
          simpa [route, hslot] using a.2
        have hd : d ∈ I.image := by
          have hmemUnion :
              (Sum.inl d : Slot) ∈
                (I.image.image
                    (Sum.inl :
                      finiteBoundaryGhostCollapsedTwoPointSourceData n v →
                        Slot)) ∪
                  ({Sum.inr ()} : Finset Slot) := by
            simpa only [atoms] using hmem
          rcases Finset.mem_union.mp hmemUnion with hmain | hempty
          · rcases Finset.mem_image.mp hmain with ⟨d', hd', hd'eq⟩
            exact (Sum.inl.inj hd'eq).symm ▸ hd'
          · exact False.elim (Sum.inl_ne_inr (Finset.mem_singleton.mp hempty))
        have hpays := hmainShareLe d hd
        simpa [route, demand, hslot] using hpays
    | inr u =>
        simpa [route, demand, hslot] using hemptyShareLe

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    ∃ Atom : Type,
      ∃ atoms : Finset Atom,
        ∃ demand : Atom → ℝ,
          ∃ route :
              Atom →
                Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit,
            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
              R ≤ ∑ a ∈ atoms, demand a ∧
                (∀ a, a ∈ atoms →
                  match route a with
                  | Sum.inl d => d ∈ I.image
                  | Sum.inr _ => True) ∧
                  Set.InjOn route atoms ∧
                    (∀ a, a ∈ atoms →
                      demand a ≤
                        match route a with
                        | Sum.inl d => mainGap d
                        | Sum.inr _ => emptyGap)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, candidateSlots, hdemandNonneg, hRle, hHall,
      hcandidateCompatible⟩
  classical
  rcases
    finiteHall_exists_injOn_of_hall_with_default
      (atoms := atoms) (candidateSlots := candidateSlots)
      (defaultSlot := (
        Sum.inr () :
          Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit))
      hHall with
    ⟨route, hrouteMem, hrouteInjective⟩
  refine
    ⟨Atom, atoms, demand, route, hdemandNonneg, hRle, ?_, hrouteInjective,
      ?_⟩
  · intro a ha
    have hcompat := hcandidateCompatible a ha (route a) (hrouteMem a ha)
    cases hroute : route a with
    | inl d =>
        have hcompat' : d ∈ I.image ∧ demand a ≤ mainGap d := by
          simpa [hroute] using hcompat
        exact hcompat'.1
    | inr j =>
        trivial
  · intro a ha
    have hcompat := hcandidateCompatible a ha (route a) (hrouteMem a ha)
    cases hroute : route a with
    | inl d =>
        have hcompat' : d ∈ I.image ∧ demand a ≤ mainGap d := by
          simpa [hroute] using hcompat
        exact hcompat'.2
    | inr j =>
        simpa [hroute] using hcompat

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainTerm := finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget := (I.image.card : ℝ) * mainTerm
  let emptyBudget := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainGap : finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      mainTerm -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap := emptyBudget - restoredCopy
  let mainSlots : Finset (finiteBoundaryGhostCollapsedTwoPointSourceData n v) :=
    I.image
  let emptySlots : Finset Unit := Finset.univ
  let emptyCap : Unit → ℝ := fun _ => emptyGap
  change ¬ (R ≤ 0) → ¬ (R ≤ mainGapSum) → ¬ (R ≤ emptyGap) →
    D + (boundaryMultiplicity + restoredCopy) ≤
      paid + (mainBudget + emptyBudget)
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, route, _hdemandNonneg, hRle, hrouteMap,
      hrouteInjective, hcover⟩
  have hmainCapNonneg :
      ∀ d, d ∈ mainSlots → 0 ≤ mainGap d := by
    intro d _hd
    simpa [mainGap] using
      finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_mainGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) hv d
  have hemptyCapNonneg :
      ∀ j, j ∈ emptySlots → 0 ≤ emptyCap j := by
    intro j _hj
    simpa [I, emptyGap, emptyBudget, restoredCopy, emptyCap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  have hmainGap :
      (∑ d ∈ mainSlots, mainGap d) =
        mainBudget - boundaryMultiplicity := by
    dsimp [mainSlots, mainGap, mainBudget, boundaryMultiplicity]
    calc
        (∑ d ∈ I.image,
            (mainTerm -
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                ℕ) : ℝ) *
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        (∑ _d ∈ I.image, mainTerm) -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_sub_distrib]
      _ =
        (I.image.card : ℝ) * mainTerm -
          ∑ d ∈ I.image,
            (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
              ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hmainCap :
      (∑ d ∈ mainSlots, mainGap d) + boundaryMultiplicity ≤
        mainBudget := by
    linarith
  have hemptySum :
      (∑ j ∈ emptySlots, emptyCap j) = emptyGap := by
    simp [emptySlots, emptyCap]
  have hemptyCap :
      (∑ j ∈ emptySlots, emptyCap j) + restoredCopy ≤
        emptyBudget := by
    have hemptyGap : emptyGap = emptyBudget - restoredCopy := rfl
    linarith
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤
        mainBudget + emptyBudget :=
    unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge_totalSlack
      (Atom := Atom)
      (MainSlot := finiteBoundaryGhostCollapsedTwoPointSourceData n v)
      (EmptySlot := Unit)
      (atoms := atoms) (mainSlots := mainSlots)
      (emptySlots := emptySlots)
      (R := R) (boundaryMultiplicity := boundaryMultiplicity)
      (restoredCopy := restoredCopy) (mainBudget := mainBudget)
      (emptyBudget := emptyBudget) (demand := demand)
      (mainCap := mainGap) (emptyCap := emptyCap)
      (route := route)
      (hmainCapNonneg := hmainCapNonneg)
      (hemptyCapNonneg := hemptyCapNonneg)
      (hR := hRle)
      (hrouteMap := by
        intro a ha
        cases hroute : route a with
        | inl d =>
            simpa [hroute, mainSlots] using hrouteMap a ha
        | inr j =>
            simp [emptySlots])
      (hrouteInjective := hrouteInjective)
      (hcover := by
        intro a ha
        cases hroute : route a with
        | inl d =>
            simpa [hroute] using hcover a ha
        | inr j =>
            simpa [hroute, emptyCap] using hcover a ha)
      (hmain := hmainCap)
      (hempty := hemptyCap)
  linarith [show R = D - paid from rfl]

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGap :
      finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have halloc := hn H hH Ω v hv
  rcases halloc with
    ⟨mainShare, emptyShare, _hmainNonneg, _hemptyNonneg, hRle,
      hmainShare, hemptyShare⟩
  have hsum :
      (∑ d ∈ I.image, mainShare d) ≤
        ∑ d ∈ I.image, mainGap d := by
    exact Finset.sum_le_sum fun d hd => hmainShare d hd
  have hgap :
      R ≤ (∑ d ∈ I.image, mainGap d) + emptyGap := by
    linarith
  simpa [Ωnz, cap, D, paid, R, I, mainGap, emptyGap] using hgap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGap
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGap :
      finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hgap :
      R ≤ (∑ d ∈ I.image, mainGap d) + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGap, emptyGap] using
      hn H hH Ω v hv
  refine ⟨mainGap, emptyGap, ?_, ?_, ?_, ?_, ?_⟩
  · intro d _hd
    exact
      finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_mainGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) hv d
  · simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  · exact hgap
  · intro d _hd
    exact le_rfl
  · exact le_rfl

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderLeCollapsedMainEmptyGapAllocation :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGap,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGapMassSplit
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGap :
      finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  rcases hn H hH Ω v hv with
    ⟨mainMass, emptyMass, _hmainMassNonneg, hemptyMassNonneg,
      hRle, hmainMass, hemptyMass⟩
  have hRgap :
      R ≤ mainGapSum + emptyMass := by
    linarith
  refine ⟨mainGap, emptyMass, ?_, hemptyMassNonneg, ?_, ?_, hemptyMass⟩
  · intro d _hd
    exact
      finiteBoundaryGhostCollapsedTwoPointSourceData_boundaryMultiplicity_mainGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) hv d
  · simpa [Ωnz, cap, D, paid, R, I, mainGap, mainGapSum, emptyGap] using
      hRgap
  · intro d _hd
    exact le_rfl

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGap :
      finiteBoundaryGhostCollapsedTwoPointSourceData n v → ℝ :=
    fun d =>
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let mainGapSum := ∑ d ∈ I.image, mainGap d
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  rcases hn H hH Ω v hv with
    ⟨mainShare, emptyShare, hmainNonneg, hemptyNonneg, hRle,
      hmainShare, hemptyShare⟩
  have hmainMassNonneg :
      0 ≤ ∑ d ∈ I.image, mainShare d := by
    exact Finset.sum_nonneg fun d hd => hmainNonneg d hd
  have hmainMassLe :
      (∑ d ∈ I.image, mainShare d) ≤ mainGapSum := by
    exact Finset.sum_le_sum fun d hd => hmainShare d hd
  refine ⟨∑ d ∈ I.image, mainShare d, emptyShare, hmainMassNonneg,
    hemptyNonneg, ?_, ?_, hemptyShare⟩
  · simpa [Ωnz, cap, D, paid, R, I, mainGap, mainGapSum, emptyGap] using
      hRle
  · exact hmainMassLe

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_iff_unpaidRemainderLeCollapsedMainEmptyGapAllocation :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGapMassSplit,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderLeCollapsedMainEmptyGapMassSplit :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical :=
  ⟨fun hgap =>
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
        (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGap
          hgap),
    fun hsplit =>
      residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
        (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGapMassSplit
          hsplit)⟩

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderNonpositive
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hRnonpos : R ≤ 0 := by
    simpa [Ωnz, cap, D, paid, R] using hn H hH Ω v hv
  have hmainGapNonneg : 0 ≤ mainGapSum := by
    simpa [I, mainGapSum] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have hemptyGapNonneg : 0 ≤ emptyGap := by
    simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  refine ⟨0, 0, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · linarith
  · exact hmainGapNonneg
  · exact hemptyGapNonneg

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedMainGapSum
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hRmain : R ≤ mainGapSum := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum] using hn H hH Ω v hv
  have hmainGapNonneg : 0 ≤ mainGapSum := by
    simpa [I, mainGapSum] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have hemptyGapNonneg : 0 ≤ emptyGap := by
    simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  refine ⟨max R 0, 0, ?_, by norm_num, ?_, ?_, ?_⟩
  · exact le_max_right R 0
  · have hRmax : R ≤ max R 0 := le_max_left R 0
    linarith
  · exact max_le hRmain hmainGapNonneg
  · exact hemptyGapNonneg

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedEmptyGap
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hRempty : R ≤ emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, emptyGap] using hn H hH Ω v hv
  have hmainGapNonneg : 0 ≤ mainGapSum := by
    simpa [I, mainGapSum] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have hemptyGapNonneg : 0 ≤ emptyGap := by
    simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  refine ⟨0, max R 0, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact le_max_right R 0
  · have hRmax : R ≤ max R 0 := le_max_left R 0
    linarith
  · exact hmainGapNonneg
  · exact max_le hRempty hemptyGapNonneg

theorem unpaidRemainderReservoirBranchPredicate_exists_iff
    {R mainGapSum emptyGap : ℝ} :
    (∃ branch : UnpaidRemainderReservoirBranch,
      unpaidRemainderReservoirBranchPredicate branch R mainGapSum emptyGap) ↔
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap := by
  constructor
  · rintro ⟨branch, hbranch⟩
    cases branch with
    | nonpositive =>
        left
        simpa [unpaidRemainderReservoirBranchPredicate] using hbranch
    | mainGap =>
        right
        left
        simpa [unpaidRemainderReservoirBranchPredicate] using hbranch
    | emptyGap =>
        right
        right
        simpa [unpaidRemainderReservoirBranchPredicate] using hbranch
  · intro hbranch
    rcases hbranch with hnonpos | hmain | hempty
    · exact
        ⟨UnpaidRemainderReservoirBranch.nonpositive,
          by simpa [unpaidRemainderReservoirBranchPredicate] using hnonpos⟩
    · exact
        ⟨UnpaidRemainderReservoirBranch.mainGap,
          by simpa [unpaidRemainderReservoirBranchPredicate] using hmain⟩
    · exact
        ⟨UnpaidRemainderReservoirBranch.emptyGap,
          by simpa [unpaidRemainderReservoirBranchPredicate] using hempty⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hdisj : R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    (unpaidRemainderReservoirBranchPredicate_exists_iff
      (R := R) (mainGapSum := mainGapSum) (emptyGap := emptyGap)).mpr hdisj

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunction_of_unpaidRemainderReservoirBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hbranch :
      ∃ branch : UnpaidRemainderReservoirBranch,
        unpaidRemainderReservoirBranchPredicate branch R mainGapSum emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    (unpaidRemainderReservoirBranchPredicate_exists_iff
      (R := R) (mainGapSum := mainGapSum) (emptyGap := emptyGap)).mp hbranch

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_iff_unpaidRemainderReservoirBranchDisjunction :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunction_of_unpaidRemainderReservoirBranchCover,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchDisjunction⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchSelector
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  refine ⟨chooseBranch β H Ωnz v, ?_⟩
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    hn H hH Ω v hv


theorem unpaidRemainderReservoirMassSplit_of_branchCover
    {R mainGapSum emptyGap : ℝ}
    (hmainGapNonneg : 0 ≤ mainGapSum)
    (hemptyGapNonneg : 0 ≤ emptyGap)
    (hbranch :
      ∃ branch : UnpaidRemainderReservoirBranch,
        unpaidRemainderReservoirBranchPredicate branch R mainGapSum emptyGap) :
    ∃ mainMass emptyMass : ℝ,
      0 ≤ mainMass ∧
        0 ≤ emptyMass ∧
        R ≤ mainMass + emptyMass ∧
        mainMass ≤ mainGapSum ∧
        emptyMass ≤ emptyGap := by
  rcases hbranch with ⟨branch, hbranch⟩
  cases branch with
  | nonpositive =>
      have hRnonpos : R ≤ 0 := by
        simpa [unpaidRemainderReservoirBranchPredicate] using hbranch
      refine ⟨0, 0, by norm_num, by norm_num, ?_, ?_, ?_⟩
      · linarith
      · exact hmainGapNonneg
      · exact hemptyGapNonneg
  | mainGap =>
      have hRmain : R ≤ mainGapSum := by
        simpa [unpaidRemainderReservoirBranchPredicate] using hbranch
      refine ⟨max R 0, 0, ?_, by norm_num, ?_, ?_, ?_⟩
      · exact le_max_right R 0
      · have hRmax : R ≤ max R 0 := le_max_left R 0
        linarith
      · exact max_le hRmain hmainGapNonneg
      · exact hemptyGapNonneg
  | emptyGap =>
      have hRempty : R ≤ emptyGap := by
        simpa [unpaidRemainderReservoirBranchPredicate] using hbranch
      refine ⟨0, max R 0, by norm_num, ?_, ?_, ?_, ?_⟩
      · exact le_max_right R 0
      · have hRmax : R ≤ max R 0 := le_max_left R 0
        linarith
      · exact hmainGapNonneg
      · exact max_le hRempty hemptyGapNonneg

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hbranch :
      ∃ branch : UnpaidRemainderReservoirBranch,
        unpaidRemainderReservoirBranchPredicate branch R mainGapSum emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  have hmainGapNonneg : 0 ≤ mainGapSum := by
    simpa [I, mainGapSum] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have hemptyGapNonneg : 0 ≤ emptyGap := by
    simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    unpaidRemainderReservoirMassSplit_of_branchCover
      hmainGapNonneg hemptyGapNonneg hbranch

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchDisjunction
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchSelector
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchSelector
      h)

theorem unpaidRemainderReservoirSplitBranchPredicate_of_reservoirBranchPredicate
    {R mainGapSum emptyGap : ℝ}
    {branch : UnpaidRemainderReservoirBranch}
    (hbranch :
      unpaidRemainderReservoirBranchPredicate branch R mainGapSum emptyGap) :
    ∃ splitBranch : UnpaidRemainderReservoirSplitBranch,
      unpaidRemainderReservoirSplitBranchPredicate
        splitBranch R mainGapSum emptyGap := by
  cases branch with
  | nonpositive =>
      exact
        ⟨UnpaidRemainderReservoirSplitBranch.nonpositive,
          by
            simpa [unpaidRemainderReservoirBranchPredicate,
              unpaidRemainderReservoirSplitBranchPredicate] using hbranch⟩
  | mainGap =>
      exact
        ⟨UnpaidRemainderReservoirSplitBranch.mainGap,
          by
            simpa [unpaidRemainderReservoirBranchPredicate,
              unpaidRemainderReservoirSplitBranchPredicate] using hbranch⟩
  | emptyGap =>
      exact
        ⟨UnpaidRemainderReservoirSplitBranch.emptyGap,
          by
            simpa [unpaidRemainderReservoirBranchPredicate,
              unpaidRemainderReservoirSplitBranchPredicate] using hbranch⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  rcases hn H hH Ω v hv with ⟨branch, hbranch⟩
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    unpaidRemainderReservoirSplitBranchPredicate_of_reservoirBranchPredicate
      (R := R) (mainGapSum := mainGapSum) (emptyGap := emptyGap)
      (branch := branch) hbranch

theorem unpaidRemainderReservoirSplitBranchPredicate_exists_iff
    {R mainGapSum emptyGap : ℝ} :
    (∃ branch : UnpaidRemainderReservoirSplitBranch,
      unpaidRemainderReservoirSplitBranchPredicate branch R mainGapSum emptyGap) ↔
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap := by
  constructor
  · rintro ⟨branch, hbranch⟩
    cases branch with
    | nonpositive =>
        left
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
    | mainGap =>
        right
        left
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
    | emptyGap =>
        right
        right
        left
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
    | mixedGap =>
        right
        right
        right
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
  · intro hbranch
    rcases hbranch with hnonpos | hrest
    · exact
        ⟨UnpaidRemainderReservoirSplitBranch.nonpositive,
          by simpa [unpaidRemainderReservoirSplitBranchPredicate] using hnonpos⟩
    rcases hrest with hmain | hrest
    · exact
        ⟨UnpaidRemainderReservoirSplitBranch.mainGap,
          by simpa [unpaidRemainderReservoirSplitBranchPredicate] using hmain⟩
    rcases hrest with hempty | hmixed
    · exact
        ⟨UnpaidRemainderReservoirSplitBranch.emptyGap,
          by simpa [unpaidRemainderReservoirSplitBranchPredicate] using hempty⟩
    · exact
        ⟨UnpaidRemainderReservoirSplitBranch.mixedGap,
          by simpa [unpaidRemainderReservoirSplitBranchPredicate] using hmixed⟩


theorem unpaidRemainderReservoirSplitBranchDisjunction_of_branchPredicate
    {R mainGapSum emptyGap : ℝ}
    {branch : UnpaidRemainderReservoirSplitBranch}
    (hbranch :
      unpaidRemainderReservoirSplitBranchPredicate
        branch R mainGapSum emptyGap) :
    R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
      R ≤ mainGapSum + emptyGap :=
  (unpaidRemainderReservoirSplitBranchPredicate_exists_iff
    (R := R) (mainGapSum := mainGapSum) (emptyGap := emptyGap)).mp
      ⟨branch, hbranch⟩


theorem unpaidRemainderReservoirSplitBranchDisjunction_iff_le_mainEmptyGap_of_nonneg
    {R mainGapSum emptyGap : ℝ}
    (hmainGapNonneg : 0 ≤ mainGapSum)
    (hemptyGapNonneg : 0 ≤ emptyGap) :
    (R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
      R ≤ mainGapSum + emptyGap) ↔
      R ≤ mainGapSum + emptyGap := by
  constructor
  · intro hdisj
    rcases hdisj with hnonpos | hrest
    · linarith
    rcases hrest with hmain | hrest
    · linarith
    rcases hrest with hempty | hmixed
    · linarith
    · exact hmixed
  · intro hmixed
    right
    right
    right
    exact hmixed

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hdisj :
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    (unpaidRemainderReservoirSplitBranchPredicate_exists_iff
      (R := R) (mainGapSum := mainGapSum) (emptyGap := emptyGap)).mpr hdisj

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderReservoirSplitBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hbranch :
      ∃ branch : UnpaidRemainderReservoirSplitBranch,
        unpaidRemainderReservoirSplitBranchPredicate
          branch R mainGapSum emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    (unpaidRemainderReservoirSplitBranchPredicate_exists_iff
      (R := R) (mainGapSum := mainGapSum) (emptyGap := emptyGap)).mp hbranch

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_iff_unpaidRemainderReservoirSplitBranchDisjunction :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderReservoirSplitBranchCover,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchDisjunction⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchSelector
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  refine ⟨chooseBranch β H Ωnz v, ?_⟩
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    hn H hH Ω v hv

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_of_unpaidRemainderReservoirSplitBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
      unpaidRemainderReservoirSplitBranchFirstTrueSelector := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hdisj :
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  simpa [unpaidRemainderReservoirSplitBranchFirstTrueSelector, Ωnz, cap, D,
    paid, R, I, mainGapSum, emptyGap] using
    unpaidRemainderReservoirSplitBranchPredicate_firstTrue_of_disjunction
      hdisj

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderReservoirSplitBranchFirstTrueSelector
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        unpaidRemainderReservoirSplitBranchFirstTrueSelector) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hbranch :
      unpaidRemainderReservoirSplitBranchPredicate
        (unpaidRemainderReservoirSplitBranchFirstTrue R mainGapSum emptyGap)
        R mainGapSum emptyGap := by
    simpa [unpaidRemainderReservoirSplitBranchFirstTrueSelector, Ωnz, cap, D,
      paid, R, I, mainGapSum, emptyGap] using hn H hH Ω v hv
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    unpaidRemainderReservoirSplitBranchDisjunction_of_branchPredicate
      (branch := unpaidRemainderReservoirSplitBranchFirstTrue R mainGapSum emptyGap)
      hbranch

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_iff_unpaidRemainderReservoirSplitBranchDisjunction :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
      unpaidRemainderReservoirSplitBranchFirstTrueSelector ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderReservoirSplitBranchFirstTrueSelector,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_of_unpaidRemainderReservoirSplitBranchDisjunction⟩


theorem unpaidRemainderReservoirMassSplit_of_splitBranchCover
    {R mainGapSum emptyGap : ℝ}
    (hmainGapNonneg : 0 ≤ mainGapSum)
    (hemptyGapNonneg : 0 ≤ emptyGap)
    (hbranch :
      ∃ branch : UnpaidRemainderReservoirSplitBranch,
        unpaidRemainderReservoirSplitBranchPredicate branch R mainGapSum emptyGap) :
    ∃ mainMass emptyMass : ℝ,
      0 ≤ mainMass ∧
        0 ≤ emptyMass ∧
        R ≤ mainMass + emptyMass ∧
        mainMass ≤ mainGapSum ∧
        emptyMass ≤ emptyGap := by
  rcases hbranch with ⟨branch, hbranch⟩
  cases branch with
  | nonpositive =>
      have hRnonpos : R ≤ 0 := by
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
      refine ⟨0, 0, by norm_num, by norm_num, ?_, ?_, ?_⟩
      · linarith
      · exact hmainGapNonneg
      · exact hemptyGapNonneg
  | mainGap =>
      have hRmain : R ≤ mainGapSum := by
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
      refine ⟨mainGapSum, 0, hmainGapNonneg, by norm_num, ?_, le_rfl, ?_⟩
      · simpa using hRmain
      · exact hemptyGapNonneg
  | emptyGap =>
      have hRempty : R ≤ emptyGap := by
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
      refine ⟨0, emptyGap, by norm_num, hemptyGapNonneg, ?_, ?_, le_rfl⟩
      · simpa using hRempty
      · exact hmainGapNonneg
  | mixedGap =>
      have hRmixed : R ≤ mainGapSum + emptyGap := by
        simpa [unpaidRemainderReservoirSplitBranchPredicate] using hbranch
      exact
        ⟨mainGapSum, emptyGap, hmainGapNonneg, hemptyGapNonneg,
          hRmixed, le_rfl, le_rfl⟩

set_option linter.style.longLine false in

theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hbranch :
      ∃ branch : UnpaidRemainderReservoirSplitBranch,
        unpaidRemainderReservoirSplitBranchPredicate
          branch R mainGapSum emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  have hmainGapNonneg : 0 ≤ mainGapSum := by
    simpa [I, mainGapSum] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have hemptyGapNonneg : 0 ≤ emptyGap := by
    simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
    unpaidRemainderReservoirMassSplit_of_splitBranchCover
      hmainGapNonneg hemptyGapNonneg hbranch

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchDisjunction
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchSelector
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchSelector
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderReservoirSplitBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hdisj :
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  have hmainGapNonneg : 0 ≤ mainGapSum := by
    simpa [I, mainGapSum] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_mainGap_sum_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have hemptyGapNonneg : 0 ≤ emptyGap := by
    simpa [I, emptyGap] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_emptyGap_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  have hgap : R ≤ mainGapSum + emptyGap :=
    (unpaidRemainderReservoirSplitBranchDisjunction_iff_le_mainEmptyGap_of_nonneg
      hmainGapNonneg hemptyGapNonneg).mp hdisj
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using hgap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderLeCollapsedMainEmptyGap
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hgap : R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  have hdisj :
      R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap ∨
        R ≤ mainGapSum + emptyGap := by
    right
    right
    right
    exact hgap
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using hdisj

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderReservoirSplitBranchDisjunction,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_of_unpaidRemainderLeCollapsedMainEmptyGap⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderReservoirSplitBranchDisjunction).trans
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_iff_unpaidRemainderLeCollapsedMainEmptyGap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_unpaidRemainderReservoirSplitFallbackMixed).trans
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderLeCollapsedMainEmptyGap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_unpaidRemainderReservoirSplitFallbackMixed).trans
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderLeCollapsedMainEmptyGap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_unpaidRemainderReservoirSplitFallbackMixed).trans
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderLeCollapsedMainEmptyGap

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderLeCollapsedMainEmptyGap
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let mainGapSum :=
    ∑ d ∈ I.image,
      (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
        (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let emptyGap :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
      (∑ d ∈ I.image,
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  have hmixed : R ≤ mainGapSum + emptyGap := by
    simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap] using
      hn H hH Ω v hv
  refine ⟨UnpaidRemainderReservoirSplitBranch.mixedGap, ?_⟩
  simpa [Ωnz, cap, D, paid, R, I, mainGapSum, emptyGap,
    unpaidRemainderReservoirSplitBranchPredicate] using hmixed

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  ⟨fun hsplit =>
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderLeCollapsedMainEmptyGapMassSplit).mpr
        (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchCover
          hsplit),
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderLeCollapsedMainEmptyGap⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
      unpaidRemainderReservoirSplitBranchFirstTrueSelector ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical := by
  constructor
  · intro hselector
    exact
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
        (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchDisjunction
          ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_iff_unpaidRemainderReservoirSplitBranchDisjunction).mp
            hselector))
  · intro hgap
    exact
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_iff_unpaidRemainderReservoirSplitBranchDisjunction).mpr
        ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_iff_unpaidRemainderReservoirSplitBranchDisjunction).mp
          ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
            hgap))

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_unpaidRemainderPlusBoundaryMultiplicityMainAndImageWeightEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  rcases hn H hH Ω v hv with ⟨hmain, hempty⟩
  refine ⟨R, 0, ?_, ?_, ?_⟩
  · linarith
  · simpa [Ωnz, cap, D, paid, R, I] using hmain
  · simpa [Ωnz, cap, D, paid, R, I] using hempty

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  rcases hn H hH Ω v hv with ⟨hmain, hempty⟩
  refine ⟨0, R, ?_, ?_, ?_⟩
  · linarith
  · simpa [Ωnz, cap, D, paid, R, I] using hmain
  · simpa [Ωnz, cap, D, paid, R, I] using hempty

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget :=
    (I.image.card : ℝ) *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let emptyBudget :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htotal :
      R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
    simpa [Ωnz, cap, D, paid, R, I, boundaryMultiplicity, restoredCopy,
      mainBudget, emptyBudget] using hn H hH Ω v hv
  refine
    ⟨mainBudget - boundaryMultiplicity, emptyBudget - restoredCopy, ?_, ?_,
      ?_⟩
  · linarith
  · linarith
  · linarith

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let mainBudget :=
    (I.image.card : ℝ) *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let emptyBudget :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  rcases hn H hH Ω v hv with ⟨mainR, emptyR, hRle, hmain, hempty⟩
  have hmain' : mainR + boundaryMultiplicity ≤ mainBudget := by
    simpa [Ωnz, cap, D, paid, R, I, boundaryMultiplicity, mainBudget] using
      hmain
  have hempty' : emptyR + restoredCopy ≤ emptyBudget := by
    simpa [Ωnz, cap, D, paid, R, I, restoredCopy, emptyBudget] using
      hempty
  have htotal : R + (boundaryMultiplicity + restoredCopy) ≤
      mainBudget + emptyBudget := by
    calc
      R + (boundaryMultiplicity + restoredCopy) ≤
          (mainR + emptyR) + (boundaryMultiplicity + restoredCopy) := by
        linarith
      _ = (mainR + boundaryMultiplicity) + (emptyR + restoredCopy) := by
        ring
      _ ≤ mainBudget + emptyBudget :=
        add_le_add hmain' hempty'
  simpa [Ωnz, cap, D, paid, R, I, boundaryMultiplicity, restoredCopy,
    mainBudget, emptyBudget] using htotal

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical :=
  ⟨fun hgap =>
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit).mp
        ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
          hgap),
    fun hsplit =>
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
        ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit).mpr
          hsplit)⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let targetMultiplicity :=
    ∑ d ∈ I.image,
      ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let mainBudget :=
    (I.image.card : ℝ) *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
  let emptyBudget :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let mainEmpty := mainBudget + emptyBudget
  rcases hn H hH Ω v hv with ⟨mainR, emptyR, hRle, hmain, hempty⟩
  have hmain' : mainR + boundaryMultiplicity ≤ mainBudget := by
    simpa [Ωnz, cap, D, paid, R, I, boundaryMultiplicity, mainBudget] using
      hmain
  have hempty' : emptyR + restoredCopy ≤ emptyBudget := by
    simpa [Ωnz, cap, D, paid, R, I, restoredCopy, emptyBudget] using
      hempty
  have htarget_split : targetMultiplicity = boundaryMultiplicity + restoredCopy := by
    dsimp [targetMultiplicity, boundaryMultiplicity, restoredCopy]
    calc
      (∑ d ∈ I.image,
          ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        ∑ d ∈ I.image,
          ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
            ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) +
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          refine Finset.sum_congr rfl ?_
          intro d _hd
          have hcast :
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
                ℕ) : ℝ)) =
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) + 1) := by
            norm_num
          rw [hcast]
          ring
      _ =
        (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
            ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) +
          ∑ d ∈ I.image,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
          rw [Finset.sum_add_distrib]
  have hsplitBudget :
      R + (boundaryMultiplicity + restoredCopy) ≤ mainBudget + emptyBudget := by
    calc
      R + (boundaryMultiplicity + restoredCopy) ≤
          (mainR + emptyR) + (boundaryMultiplicity + restoredCopy) := by
        linarith
      _ = (mainR + boundaryMultiplicity) + (emptyR + restoredCopy) := by
        ring
      _ ≤ mainBudget + emptyBudget :=
        add_le_add hmain' hempty'
  have htarget : R + targetMultiplicity ≤ mainEmpty := by
    calc
      R + targetMultiplicity = R + (boundaryMultiplicity + restoredCopy) := by
        rw [htarget_split]
      _ ≤ mainBudget + emptyBudget := hsplitBudget
      _ = mainEmpty := rfl
  simpa [Ωnz, cap, D, paid, R, I, targetMultiplicity, mainEmpty, mainBudget,
    emptyBudget] using htarget

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical := by
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let boundaryMultiplicity :=
    ∑ d ∈ I.image,
      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let restoredCopy :=
    ∑ d ∈ I.image,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
  let targetMultiplicity :=
    ∑ d ∈ I.image,
      ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let mainEmpty :=
    (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htarget :
      R + targetMultiplicity ≤ mainEmpty := by
    simpa [Ωnz, cap, D, paid, R, I, targetMultiplicity, mainEmpty] using
      hn H hH Ω v hv
  have htarget_split : targetMultiplicity = boundaryMultiplicity + restoredCopy := by
    dsimp [targetMultiplicity, boundaryMultiplicity, restoredCopy]
    calc
      (∑ d ∈ I.image,
          ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))) =
        ∑ d ∈ I.image,
          ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
            ℕ) : ℝ) *
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) +
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
          refine Finset.sum_congr rfl ?_
          intro d _hd
          have hcast :
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
                ℕ) : ℝ)) =
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) + 1) := by
            norm_num
          rw [hcast]
          ring
      _ =
        (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) :
            ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) +
          ∑ d ∈ I.image,
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
          rw [Finset.sum_add_distrib]
  have hadd : R + (boundaryMultiplicity + restoredCopy) ≤ mainEmpty := by
    calc
      R + (boundaryMultiplicity + restoredCopy) = R + targetMultiplicity := by
        rw [htarget_split]
      _ ≤ mainEmpty := htarget
  simpa [Ωnz, cap, D, paid, R, I, boundaryMultiplicity, restoredCopy,
    mainEmpty] using hadd

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical :=
  ⟨fun htarget =>
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
        ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty).mp
          htarget),
    fun hgap =>
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty).mpr
        ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
          hgap)⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderNonpositive
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [h β hβpos hβc,
      sourceActiveCollapsedVertexTargetMultiplicityMainEmptyWeightNonzeroBranch
        β hβpos hβc] with n hn hsource
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
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let targetMultiplicity :=
    ∑ d ∈ I.image,
      ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let mainEmpty :=
    (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have hRnonpos : R ≤ 0 := by
    simpa [Ωnz, cap, D, paid, R] using hn H hH Ω v hv
  have htarget : targetMultiplicity ≤ mainEmpty := by
    simpa [Ωnz, I, targetMultiplicity, mainEmpty] using
      hsource H hH Ω v hv
  have hgoal : R + targetMultiplicity ≤ mainEmpty := by
    linarith
  simpa [Ωnz, cap, D, paid, R, I, targetMultiplicity, mainEmpty] using hgoal

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderLeCollapsedMainGapSum
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderLeCollapsedMainEmptyGapMassSplit).mpr
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedMainGapSum
        h))

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderLeCollapsedEmptyGap
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderLeCollapsedMainEmptyGapMassSplit).mpr
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedEmptyGap
        h))

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_iff_unpaidRemainderLeCollapsedMainEmptyGapMassSplit).mpr
      (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchCover
        h))

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchDisjunction
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirBranchSelector
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchSelector
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitBranchCover
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitBranchDisjunction
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunction_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixed
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixed_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedPaymentDominates
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitBranchSelector
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitBranchCover
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchSelector
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitBranchFirstTrueSelector
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        unpaidRemainderReservoirSplitBranchFirstTrueSelector) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical :=
  (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_iff_unpaidRemainderLeCollapsedMainEmptyGap).mpr
    ((residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchFirstTrueSelector_iff_unpaidRemainderLeCollapsedMainEmptyGap).mp
      h)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfile_of_unpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  let collapsedActive :=
    ∑ d ∈ I.image,
      (((I.fiber d).card : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
  let targetMultiplicity :=
    ∑ d ∈ I.image,
      ((((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) : ℝ) *
        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
  let mainEmpty :=
    (I.image.card : ℝ) *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have hfiber : collapsedActive ≤ targetMultiplicity := by
    simpa [I, collapsedActive, targetMultiplicity] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have htarget :
      R + targetMultiplicity ≤ mainEmpty := by
    simpa [Ωnz, cap, D, paid, R, I, targetMultiplicity, mainEmpty] using
      hn H hH Ω v hv
  have hprofile : mainEmpty ≤ profile := by
    simpa [I, profile, mainEmpty] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_mul_main_add_empty_le_boundaryFiberSourcePairVertexProfile
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH)
        Ωnz hv
  have hleft : R + collapsedActive ≤ R + targetMultiplicity := by
    linarith
  have hcollapsed : R + collapsedActive ≤ profile :=
    hleft.trans (htarget.trans hprofile)
  simpa [Ωnz, cap, D, paid, R, profile, I, collapsedActive] using hcollapsed

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_of_unpaidRemainderPlusActiveLeProfile
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let active :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
      β H n Ωnz v
  let slack := profile - active
  have hprofile :
      R + active ≤ profile := by
    simpa [Ωnz, cap, D, paid, R, profile, active] using
      hn H hH Ω v hv
  have hRle : R ≤ slack := by
    linarith
  simpa [Ωnz, cap, D, paid, R, slack, profile, active] using hRle

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfile_of_unpaidRemainderLeProfileSlack
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let active :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
      β H n Ωnz v
  let slack := profile - active
  have hRle :
      R ≤ slack := by
    simpa [Ωnz, cap, D, paid, R, slack, profile, active] using
      hn H hH Ω v hv
  have hprofile : R + active ≤ profile := by
    linarith
  simpa [Ωnz, cap, D, paid, R, profile, active] using hprofile

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_iff_unpaidRemainderPlusActiveLeProfile :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfile_of_unpaidRemainderLeProfileSlack,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_of_unpaidRemainderPlusActiveLeProfile⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_of_paidPlusProfileDominatesSimonPlusActive
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let active :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
      β H n Ωnz v
  let slack := profile - active
  have hdom :
      D + active ≤ paid + profile := by
    simpa [Ωnz, cap, D, paid, profile, active] using hn H hH Ω v hv
  have hRle : R ≤ slack := by
    linarith
  simpa [Ωnz, cap, D, paid, R, slack, profile, active] using hRle

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActive_of_unpaidRemainderLeProfileSlack
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical := by
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
  let profile :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v
  let active :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
      β H n Ωnz v
  let slack := profile - active
  have hRle :
      R ≤ slack := by
    simpa [Ωnz, cap, D, paid, R, slack, profile, active] using
      hn H hH Ω v hv
  have hdom : D + active ≤ paid + profile := by
    linarith
  simpa [Ωnz, cap, D, paid, profile, active] using hdom

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_iff_paidPlusProfileDominatesSimonPlusActive :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical ↔
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical :=
  ⟨residualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActive_of_unpaidRemainderLeProfileSlack,
    residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_of_paidPlusProfileDominatesSimonPlusActive⟩

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment_of_rawStrictTotal_unpaidRemainderLeProfileSlack
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hRleSlack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hrawStrict β hβpos hβc, hRleSlack β hβpos hβc] with
    n hnStrict hnRleSlack
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
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
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
  have hstrict :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) < R := by
    simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail, row] using
      hnStrict H hH Ω v hv
  have hRle :
      R ≤ slack := by
    simpa [Ωnz, cap, D, paid, R, slack] using
      hnRleSlack H hH Ω v hv
  exact le_trans (le_of_lt hstrict) hRle

set_option linter.style.longLine false in


theorem liveSingletonOptionShareSchedulePayment_of_residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hraw β hβpos hβc] with n hnR hnRaw
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
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
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
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hrawv :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) ≤ slack := by
    simpa [Ωnz, slack, liveOptions, remaining, tail, row] using
      hnRaw H hH Ω v hv
  have hremaining :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
          β H Ωnz v * R = remaining := by
    simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
      liveSingletonOptionNormalizedRemainingShare, Ωnz, cap, D, paid, R,
      remaining] using
      (div_mul_cancel₀ remaining hRpos.ne')
  have htail :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
          β H Ωnz v * R = tail := by
    simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
      liveSingletonOptionNormalizedTailShare, Ωnz, cap, D, paid, R, tail] using
      (div_mul_cancel₀ tail hRpos.ne')
  have hrow :
      ∀ x,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
            β H Ωnz v x * R = row x := by
    intro x
    simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
      Ωnz, cap, D, paid, R, row] using
      (finset_sum_div_mul_cancel₀
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true ({x} : Finset (Option (FK.boxVerts 3 n))))
        (fun E => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E)
        hRpos.ne')
  have hsum :
      (∑ x ∈ liveOptions,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
            β H Ωnz v x * R) =
        ∑ x ∈ liveOptions, row x := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    exact hrow x
  have hlhs :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
            β H Ωnz v * R +
          ((∑ x ∈ liveOptions,
              liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
                β H Ωnz v x * R) +
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
              β H Ωnz v * R) =
        remaining + ((∑ x ∈ liveOptions, row x) + tail) := by
    rw [hremaining, hsum, htail]
  exact hlhs.trans_le hrawv

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment_of_liveSingletonOptionShareSchedulePayment
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hpayment β hβpos hβc] with n hnR hnPayment
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
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
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
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hpayv :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
            β H Ωnz v * R +
          ((∑ x ∈ liveOptions,
              liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
                β H Ωnz v x * R) +
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
              β H Ωnz v * R) ≤ slack := by
    simpa [Ωnz, cap, D, paid, R, slack, liveOptions] using
      hnPayment H hH Ω v hv
  have hremaining :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
          β H Ωnz v * R = remaining := by
    simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
      liveSingletonOptionNormalizedRemainingShare, Ωnz, cap, D, paid, R,
      remaining] using
      (div_mul_cancel₀ remaining hRpos.ne')
  have htail :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
          β H Ωnz v * R = tail := by
    simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
      liveSingletonOptionNormalizedTailShare, Ωnz, cap, D, paid, R, tail] using
      (div_mul_cancel₀ tail hRpos.ne')
  have hrow :
      ∀ x,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
            β H Ωnz v x * R = row x := by
    intro x
    simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
      Ωnz, cap, D, paid, R, row] using
      (finset_sum_div_mul_cancel₀
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true ({x} : Finset (Option (FK.boxVerts 3 n))))
        (fun E => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E)
        hRpos.ne')
  have hsum :
      (∑ x ∈ liveOptions,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
            β H Ωnz v x * R) =
        ∑ x ∈ liveOptions, row x := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    exact hrow x
  have hlhs :
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
            β H Ωnz v * R +
          ((∑ x ∈ liveOptions,
              liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
                β H Ωnz v x * R) +
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
              β H Ωnz v * R) =
        remaining + ((∑ x ∈ liveOptions, row x) + tail) := by
    rw [hremaining, hsum, htail]
  exact (le_of_eq hlhs.symm).trans hpayv

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment_iff_liveSingletonOptionShareSchedulePayment
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical ↔
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical :=
  ⟨liveSingletonOptionShareSchedulePayment_of_residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment hR,
    residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment_of_liveSingletonOptionShareSchedulePayment hR⟩

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePayment_of_liveSingletonOptionShareSchedulePayment
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentWeightNonzeroPositiveSubcritical
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
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  simpa [liveSingletonOptionComponentBudgetScheduleOfShareSchedule, Ωnz, cap, D,
    paid, R, slack, liveOptions] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment_of_componentBudgetSchedulePayment
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionComponentBudgetScheduleOfShareSchedule schedule)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
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
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  simpa [liveSingletonOptionComponentBudgetScheduleOfShareSchedule, Ωnz, cap, D,
    paid, R, slack, liveOptions] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment_iff_componentBudgetSchedulePayment
    (schedule : LiveSingletonOptionShareSchedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule ↔
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionComponentBudgetScheduleOfShareSchedule schedule) :=
  ⟨inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePayment_of_liveSingletonOptionShareSchedulePayment,
    inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment_of_componentBudgetSchedulePayment⟩

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment_labelRowsCanonical_iff_pointwiseRowsCanonical
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
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label) ↔
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical := by
  constructor
  · intro hlabel β hβpos hβc
    filter_upwards [hlabel β hβpos hβc] with n hn
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
    let slack :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v
    let liveOptions :=
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
        v Ωnz true true true
    have hsingleton :
        ∀ x,
          (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
              label).singletonShare β H Ωnz v x =
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
              β H Ωnz v x := by
      intro x
      simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical] using
        (liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRows_singletonShare_eq_pointwiseRows
          (label := label)
          (remainingShare := fun {n} β H Ω v =>
            liveSingletonOptionNormalizedRemainingShare (n := n) β H Ω v)
          (tailShare := fun {n} β H Ω v =>
            liveSingletonOptionNormalizedTailShare (n := n) β H Ω v)
          β H Ωnz v x)
    have hsum :
        (∑ x ∈ liveOptions,
          (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
              label).singletonShare β H Ωnz v x * R) =
          ∑ x ∈ liveOptions,
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
              β H Ωnz v x * R := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      rw [hsingleton x]
    have hpay := hn H hH Ω v hv
    have hsame :
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
              β H Ωnz v * R +
            ((∑ x ∈ liveOptions,
                liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
                  β H Ωnz v x * R) +
              liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
                β H Ωnz v * R) =
          (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
                label).remainingShare β H Ωnz v * R +
            ((∑ x ∈ liveOptions,
                (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
                  label).singletonShare β H Ωnz v x * R) +
              (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
                label).tailShare β H Ωnz v * R) := by
      simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows] using hsum.symm
    exact hsame.trans_le (by
      simpa [Ωnz, cap, D, paid, R, slack, liveOptions] using hpay)
  · intro hpoint β hβpos hβc
    filter_upwards [hpoint β hβpos hβc] with n hn
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
    let slack :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v
    let liveOptions :=
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
        v Ωnz true true true
    have hsingleton :
        ∀ x,
          (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
              label).singletonShare β H Ωnz v x =
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
              β H Ωnz v x := by
      intro x
      simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical] using
        (liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRows_singletonShare_eq_pointwiseRows
          (label := label)
          (remainingShare := fun {n} β H Ω v =>
            liveSingletonOptionNormalizedRemainingShare (n := n) β H Ω v)
          (tailShare := fun {n} β H Ω v =>
            liveSingletonOptionNormalizedTailShare (n := n) β H Ω v)
          β H Ωnz v x)
    have hsum :
        (∑ x ∈ liveOptions,
          (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
              label).singletonShare β H Ωnz v x * R) =
          ∑ x ∈ liveOptions,
            liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
              β H Ωnz v x * R := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      rw [hsingleton x]
    have hpay := hn H hH Ω v hv
    have hsame :
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
                label).remainingShare β H Ωnz v * R +
            ((∑ x ∈ liveOptions,
                (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
                  label).singletonShare β H Ωnz v x * R) +
              (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
                label).tailShare β H Ωnz v * R) =
          liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.remainingShare
              β H Ωnz v * R +
            ((∑ x ∈ liveOptions,
                liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.singletonShare
                  β H Ωnz v x * R) +
              liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical.tailShare
                β H Ωnz v * R) := by
      simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows] using hsum
    exact hsame.trans_le (by
      simpa [Ωnz, cap, D, paid, R, slack, liveOptions] using hpay)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail_of_components
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
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentWeightNonzeroPositiveSubcritical
        budget) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailWeightNonzeroPositiveSubcritical
      budget := by
  intro β hβpos hβc
  filter_upwards
    [hremaining β hβpos hβc, htail β hβpos hβc,
      hsingleton β hβpos hβc, hpayment β hβpos hβc] with
    n hnRemaining hnTail hnSingleton hnPayment
  intro H hH Ω v hv
  exact
    ⟨hnRemaining H hH Ω v hv,
      hnTail H hH Ω v hv,
      hnSingleton H hH Ω v hv,
      hnPayment H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailWeightNonzeroPositiveSubcritical
        budget) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  rcases hn H hH Ω v hv with
    ⟨hremaining, htail, hsingleton, hpayment⟩
  refine
    ⟨budget.remainingBudget β H Ωnz v,
      budget.tailBudget β H Ωnz v,
      fun x => budget.singletonBudget β H Ωnz v x,
      hremaining, htail, hsingleton, ?_⟩
  simpa [liveOptions, Ωnz] using hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail_of_liveSingletonOptionShareSchedulePayment
    {schedule : LiveSingletonOptionShareSchedule}
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailWeightNonzeroPositiveSubcritical
      (liveSingletonOptionComponentBudgetScheduleOfShareSchedule schedule) := by
  intro β hβpos hβc
  have hcomponent :=
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorption_of_liveSingletonOptionShareSchedule
      hshare
  have hprofilePayment :=
    inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePayment_of_liveSingletonOptionShareSchedulePayment
      hpayment
  filter_upwards [hcomponent β hβpos hβc,
    hprofilePayment β hβpos hβc] with n hnComponent hnPayment
  intro H hH Ω v hv
  rcases hnComponent H hH Ω v hv with
    ⟨hremaining, htail, hsingleton, _hdenominatorPayment⟩
  exact ⟨hremaining, htail, hsingleton, hnPayment H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  rcases hn H hH Ω v hv with
    ⟨remainingBudget, tailBudget, singletonBudget, hremaining,
      htail, hpoint, hle⟩
  refine ⟨singletonBudget, hpoint, ?_⟩
  have htailMono :
      (∑ x ∈ liveOptions, singletonBudget x) +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v ≤
        (∑ x ∈ liveOptions, singletonBudget x) + tailBudget :=
    add_le_add le_rfl htail
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        ((∑ x ∈ liveOptions, singletonBudget x) +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        remainingBudget +
          ((∑ x ∈ liveOptions, singletonBudget x) + tailBudget) :=
    add_le_add hremaining htailMono
  exact hmono.trans hle

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hle⟩
  refine ⟨remaining, tail, singletonBudget, le_rfl, le_rfl, hpoint, ?_⟩
  simpa [remaining, tail, liveOptions, Ωnz, slack] using hle

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail_iff_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailWeightNonzeroPositiveSubcritical ↔
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailWeightNonzeroPositiveSubcritical :=
  ⟨inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail,
    inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail⟩

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hle⟩
  have hcardLe :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v ≤
        ∑ x ∈ liveOptions, singletonBudget x :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_singletonOptionNonemptyClassifiedSet_singletonBudget_sum_of_boundary
      hv hpoint
  have hcardTail :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v ≤
        (∑ x ∈ liveOptions, singletonBudget x) +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v :=
    add_le_add hcardLe le_rfl
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
            β H n Ωnz v +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v +
          ((∑ x ∈ liveOptions, singletonBudget x) +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) :=
    add_le_add le_rfl hcardTail
  exact hmono.trans hle

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  rcases hn H hH Ω v hv with ⟨singletonBudget, hpoint, hle⟩
  have hcardLe :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
          β H n Ωnz v ≤
        ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
          singletonBudget x :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_le_unmarkedOptions_singletonBudget_sum
      hpoint
  have htail :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v ≤
        (∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
          singletonBudget x) +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v :=
    add_le_add hcardLe le_rfl
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
            β H n Ωnz v +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v +
          ((∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
            singletonBudget x) +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) :=
    add_le_add le_rfl htail
  exact hmono.trans hle

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  have hsplit := hn H hH Ω v hv
  have hcard :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v =
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
          β H n Ωnz v :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_residualSetContribution_of_boundary
      β H n Ωnz hv
  simpa [hcard, Ωnz, slack] using hsplit

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpoint_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  have hsplit := hn H hH Ω v hv
  simpa [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution_eq_cardOne_add_tail
      β H n Ωnz v,
    Ωnz,
    slack] using hsplit

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotal_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpoint
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotalWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  have hsplit := hn H hH Ω v hv
  simpa [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal_eq_remaining_add_ghostOriginEndpointContribution
      β H n Ωnz v,
    Ωnz,
    slack] using hsplit

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorant_of_labelFreeRawShellConcreteIccExactCardImageCanonicalTotal
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ωnz v hasGhost hasOrigin hasEndpoint k
  have htotal := hn H hH Ω v hv
  refine
    ⟨B.zero_none, B.two_none, B.two_endpoint, B.two_origin, B.two_ghost,
      B.two_ghost_endpoint, B.two_ghost_origin, fourMajorant,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · intro k _hk
    exact le_rfl
  · simpa [B, fourMajorant, Ωnz,
      SourceClassEndpointMembershipResidualShellShare15.expandedIccOfFourShareTotal]
      using htotal

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorant_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint, htotal⟩
  refine
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    cases hasGhost <;> cases hasOrigin <;> cases hasEndpoint
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourNone k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourEndpoint k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourOrigin k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourOriginEndpoint k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourGhost k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourGhostEndpoint k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourGhostOrigin k hk
    · simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]
        using hfourGhostOriginEndpoint k hk
  · simpa [Ωnz] using htotal

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorant_of_labelFreeRawShellIccExactCardImageExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorantWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, htotal⟩
  refine
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    have hkIcc :
        k ∈
          Finset.Icc
            (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
              hasGhost hasOrigin hasEndpoint)
            ((2 * n + 1) ^ 3 - 2) := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
          hv hasGhost hasOrigin hasEndpoint] using hk
    rw [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
        β H n Ωnz v hasGhost hasOrigin hasEndpoint k]
    exact hfour hasGhost hasOrigin hasEndpoint k hkIcc
  · simpa [Ωnz,
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_eq_expandedIccOfFourShareTotal_of_boundary
        hv] using htotal

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorant_of_labelFreeRawShellExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorantWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, htotal⟩
  refine
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, ?_⟩
  simpa [Ωnz,
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare_total_eq_expandedOfFourShareTotal]
    using htotal

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellMajorant_of_labelFreeRawShellExplicitMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellMajorantWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zero_none, two_none, two_endpoint, two_origin, two_ghost,
      two_ghost_endpoint, two_ghost_origin, fourMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, htotal⟩
  refine
    ⟨SourceClassEndpointMembershipResidualShellShare15.ofFourShare
        v zero_none two_none two_endpoint two_origin two_ghost
        two_ghost_endpoint two_ghost_origin fourMajorant,
      ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_fields
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (zero_none := zero_none) (two_none := two_none)
        (two_endpoint := two_endpoint) (two_origin := two_origin)
        (two_ghost := two_ghost)
        (two_ghost_endpoint := two_ghost_endpoint)
        (two_ghost_origin := two_ghost_origin)
        (fourMajorant := fourMajorant)
        hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin hfour
  · simpa [Ωnz] using htotal

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellExplicitMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellMajorant_of_labelFreeRawShellExplicitMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellExplicitMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorant_of_labelFreeRawShellExpandedMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellIccExactCardImageExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellExpandedMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorant_of_labelFreeRawShellIccExactCardImageExpandedMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellIccExactCardImageExpandedMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorant_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellConcreteIccExactCardImageCanonicalTotal
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorant_of_labelFreeRawShellConcreteIccExactCardImageCanonicalTotal
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotal_of_labelFreeRawMajorantBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotalWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let rawBudget :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
      v β H Ωnz
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
      v β H Ωnz
  rcases hn H hH Ω v hv with ⟨B, hfield, htotal⟩
  have hrawLe : rawShell ≤ B.total := by
    calc
      rawShell = rawBudget.total := by
        symm
        simpa [rawBudget, rawShell] using
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_total
            (v := v) (β := β) (H := H) (Ω := Ωnz)
      _ ≤ B.total :=
        SourceClassEndpointMembershipLiveBudget15.total_le_of_fieldwiseLe
          hfield
  have hslack :
      B.total ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    simpa [Ωnz, rawBudget] using htotal
  exact hrawLe.trans hslack

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawMajorantBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawTotal
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotal_of_labelFreeRawMajorantBudget15
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellExplicitMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawMajorantBudget15
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellExplicitMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellExplicitMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExplicitMajorant_of_labelFreeRawShellExpandedMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellIccExactCardImageExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellExpandedMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellExpandedMajorant_of_labelFreeRawShellIccExactCardImageExpandedMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellIccExactCardImageExpandedMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellIccExactCardImageExpandedMajorant_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalTotal
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageExpandedMajorant
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageExpandedMajorant_of_labelFreeRawShellConcreteIccExactCardImageCanonicalTotal
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpoint
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalTotal
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalTotal_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpoint
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpoint
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpoint_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailWeightNonzeroPositiveSubcritical
        budget) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleComponentsTail
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
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentWeightNonzeroPositiveSubcritical
        budget) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail_of_components
      hremaining htail hsingleton hpayment)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    {schedule : LiveSingletonOptionShareSchedule}
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTail_of_liveSingletonOptionShareSchedulePayment
      hshare hpayment)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleComponentsPayment
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
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_components
      hbudget hremaining htail hsingleton)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleFineComponentsPayment
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
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_fine_components
      hR hremainingNonneg htailNonneg hsingletonNonneg hstrict
      hremaining htail hsingleton)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleDerivedSignComponentsPayment
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
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_derivedSignComponents
      hR hstrict hremaining htail hsingleton)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignPayment
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
    (hrow :
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
                    schedule.singletonShare β H Ωnz v x)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseNormalizedPointwiseRowsDerivedSignComponents
      hR hstrict hremaining htail hrow)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignPayment
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
    (hrow :
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
                    schedule.singletonShare β H Ωnz v x)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseNormalizedLabelRowsDerivedSignComponents
      (schedule := schedule) (label := label) hR hstrict hremaining htail hrow)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignPaymentRemainderPositive
    {schedule : LiveSingletonOptionShareSchedule}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hrow :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignPayment
    (schedule := schedule)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := schedule) hpos)
    hstrict hremaining htail hrow hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignPaymentComponentStrictCanonicalRatioShareSum
    {schedule : LiveSingletonOptionShareSchedule}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hrow :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignPaymentRemainderPositive
    (schedule := schedule)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hstrict hremaining htail hrow hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignPaymentRemainderPositive
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
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hrow :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignPayment
    (schedule := schedule) (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := schedule) hpos)
    hstrict hremaining htail hrow hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignPaymentComponentStrictCanonicalRatioShareSum
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
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hrow :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignPaymentRemainderPositive
    (schedule := schedule) (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hstrict hremaining htail hrow hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalDerivedSignPayment
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignPayment
    (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    hR hstrict
    (liveSingletonOptionShareScheduleRemaining_of_residualCaseNormalizedPointwiseRowsCanonical
      hR)
    (liveSingletonOptionShareScheduleTail_of_residualCaseNormalizedPointwiseRowsCanonical
      hR)
    liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment_of_canonical
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPayment
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalDerivedSignPayment
    hR
    (liveSingletonOptionShareScheduleStrictTotal_of_residualCaseNormalizedPointwiseRowsCanonicalRaw
      hR hraw)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignRawProfilePayment
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPayment
    hR hrawStrict
    (liveSingletonOptionShareSchedulePayment_of_residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment
      hR hrawPayment)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeProfileSlack
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hRleSlack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignRawProfilePayment
    (liveSingletonOptionShareScheduleRemainderPositive_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      (liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal
        hrawStrict))
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalRawProfilePayment_of_rawStrictTotal_unpaidRemainderLeProfileSlack
      hrawStrict hRleSlack)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaidPlusProfileDominatesSimonPlusActive
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdom :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeProfileSlack
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_of_paidPlusProfileDominatesSimonPlusActive
      hdom)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusActiveLeProfile
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprofile :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeProfileSlack
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlack_of_unpaidRemainderPlusActiveLeProfile
      hprofile)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedActiveImageLeProfile
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcollapsed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusActiveLeProfile
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfile_of_unpaidRemainderPlusCollapsedActiveImageLeProfile
      hcollapsed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (htarget :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedActiveImageLeProfile
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfile_of_unpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
      htarget)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsplit :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
      hsplit)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_unpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
      hslack)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGap
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hgap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty_of_unpaidRemainderLeCollapsedMainEmptyGap
      hgap)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapAllocation
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (halloc :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGap
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGap_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
      halloc)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmass :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapAllocation
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocation_of_unpaidRemainderLeCollapsedMainEmptyGapMassSplit
      hmass)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderNonpositive
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hnonpos :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderNonpositive
      hnonpos)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainGapSum
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmainGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedMainGapSum
      hmainGap)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedEmptyGap
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hemptyGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderLeCollapsedEmptyGap
      hemptyGap)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchCover
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirBranchCover
      hbranch)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchDisjunction
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchCover
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchDisjunction
      hbranch)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchSelector
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchCover
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCover_of_unpaidRemainderReservoirBranchSelector
      hbranch)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchCover
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplit_of_unpaidRemainderReservoirSplitBranchCover
      hbranch)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchDisjunction
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchCover
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchDisjunction
      hbranch)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchSelector
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchCover
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCover_of_unpaidRemainderReservoirSplitBranchSelector
      hbranch)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchFirstTrueSelector
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        unpaidRemainderReservoirSplitBranchFirstTrueSelector) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchSelector
    (chooseBranch := unpaidRemainderReservoirSplitBranchFirstTrueSelector)
    hrawStrict
    hbranch

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixed
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixed
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedPaymentDominates
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedExpandedDemand
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
      hmixed)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityMainAndImageWeightEmpty
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmain :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_unpaidRemainderPlusBoundaryMultiplicityMainAndImageWeightEmpty
      hmain)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignBoundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hempty :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty
      hempty)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaymentRemainderPositive
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPayment
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      hpos)
    hraw hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaymentComponentStrictCanonicalRatioShareSum
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaymentRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaymentLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPayment
    (liveSingletonOptionShareScheduleRemainderPositive_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      hbudget)
    (liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      hbudget)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalDerivedSignPaymentRemainderPositive
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalDerivedSignPayment
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      hpos)
    hstrict hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalDerivedSignPaymentComponentStrictCanonicalRatioShareSum
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalDerivedSignPaymentRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hstrict hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalDerivedSignPayment
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
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignPayment
    (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
      label)
    (label := label)
    hR hstrict
    (liveSingletonOptionShareScheduleRemaining_of_residualCaseNormalizedLabelRowsCanonical
      (label := label) hR)
    (liveSingletonOptionShareScheduleTail_of_residualCaseNormalizedLabelRowsCanonical
      (label := label) hR)
    (liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment_of_canonical
      label)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPayment
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
        label)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalDerivedSignPayment
    (label := label)
    hR
    (liveSingletonOptionShareScheduleStrictTotal_of_residualCaseNormalizedLabelRowsCanonicalRaw
      (label := label) hR hraw)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPaymentRemainderPositive
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
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPayment
    (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label)
      hpos)
    hraw hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPaymentComponentStrictCanonicalRatioShareSum
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
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPaymentRemainderPositive
    (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPaymentLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
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
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignPayment
    (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label)
      hbudget)
    (liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotal_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      (label := label) hbudget)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalDerivedSignPaymentRemainderPositive
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
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalDerivedSignPayment
    (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label)
      hpos)
    hstrict hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalDerivedSignPaymentComponentStrictCanonicalRatioShareSum
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
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label)) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalDerivedSignPaymentRemainderPositive
    (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hstrict hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignPayment
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
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonPaymentDerivedSignComponents
      hR hstrict hremaining htail hsingletonResidual)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseSingletonDerivedSignPayment
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
        schedule)
    (hpayment :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePaymentWeightNonzeroPositiveSubcritical
        schedule) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareSchedulePayment
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonDerivedSignComponents
      hR hstrict hremaining htail hsingletonResidual)
    hpayment

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTail
      h)

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTail
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTail
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTail_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTail
      h)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_labelFreeRawMajorantBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawMajorantBudget15 h)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceAbsorption_of_labelFreeRawMajorantBudget15_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (boundaryVertexDecrementedSourceProfileMajorization_of_labelFreeRawMajorantBudget15
      hmajor)
    hsource

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_labelFreeRawMajorantBudget15_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (boundaryVertexDecrementedSourceProfileMajorization_of_labelFreeRawMajorantBudget15
      hmajor)
    hsource

set_option linter.style.longLine false in


theorem firstExitPositive_of_labelFreeRawMajorantBudget15_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (boundaryVertexDecrementedSourceProfileMajorization_of_labelFreeRawMajorantBudget15
      hmajor)
    hsource

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_labelFreeRawMajorantBudget15_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (boundaryVertexDecrementedSourceProfileMajorization_of_labelFreeRawMajorantBudget15
      hmajor)
    hsource

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_sourceClassSupportComponentSum
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical)
    (hsum :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, hsum β hβpos hβc] with
    n hnpos hnsum
  intro H hH Ω v hv
  exact ⟨hnpos H hH v hv, hnsum H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorption_of_positiveDenominatorComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨hdenomPos, coefficientBudget, hcase, htotal⟩
  have hdenomPos' : 0 < denom := by
    simpa [denom] using hdenomPos
  let oneTerm :=
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n
  let boundaryTerm :=
    cap *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v
  let emptyTerm :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  refine
    ⟨oneTerm / denom, boundaryTerm / denom, emptyTerm / denom,
      fun S => coefficientBudget S / denom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcap : 0 ≤ cap := by
      simpa [cap, boundaryCrossingCap] using
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
          Ωnz
    have hone :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH)
    exact div_nonneg (mul_nonneg hcap hone) (le_of_lt hdenomPos)
  · have hcap : 0 ≤ cap := by
      simpa [cap, boundaryCrossingCap] using
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
          Ωnz
    have hboundary :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact div_nonneg (mul_nonneg hcap hboundary) (le_of_lt hdenomPos)
  · have hempty :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact div_nonneg hempty (le_of_lt hdenomPos)
  · intro S hS
    have hsector :
        0 ≤
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v S :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v S
    have hbudgetNonneg : 0 ≤ coefficientBudget S :=
      hsector.trans (hcase S hS)
    exact div_nonneg hbudgetNonneg (le_of_lt hdenomPos)
  · calc
      oneTerm / denom + boundaryTerm / denom + emptyTerm / denom +
          (∑ S ∈ sourceClassSupport, coefficientBudget S / denom) =
          (oneTerm + boundaryTerm + emptyTerm +
              (∑ S ∈ sourceClassSupport, coefficientBudget S)) / denom := by
        rw [← Finset.sum_div]
        ring
      _ ≤ denom / denom :=
        div_le_div_of_nonneg_right
          (by simpa [oneTerm, boundaryTerm, emptyTerm, cap, sourceClassSupport,
              denom, Ωnz] using htotal)
          (le_of_lt hdenomPos')
      _ = 1 := by
        field_simp [ne_of_gt hdenomPos']
  · dsimp [oneTerm]
    rw [div_mul_cancel₀ _ hdenomPos'.ne']
  · dsimp [boundaryTerm]
    rw [div_mul_cancel₀ _ hdenomPos'.ne']
  · dsimp [emptyTerm]
    rw [div_mul_cancel₀ _ hdenomPos'.ne']
  · intro S hS
    rw [div_mul_cancel₀ _ hdenomPos'.ne']
    exact hcase S (by simpa [sourceClassSupport] using hS)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorption_of_componentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, coefficientShare,
      _honeShare, _hboundaryShare, _hemptyShare, _hcoefficientShare,
      hshareSum, hone, hboundary, hempty, hcoefficient⟩
  refine ⟨fun S => coefficientShare S * denom, ?_, ?_⟩
  · intro S hS
    exact hcoefficient S hS
  · have hdenomNonneg : 0 ≤ denom := by
      dsimp [denom]
      exact finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
    calc
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
            (∑ S ∈ sourceClassSupport, coefficientShare S * denom)
          ≤
            oneShare * denom + boundaryPairShare * denom +
              emptyBoundaryShare * denom +
              (∑ S ∈ sourceClassSupport, coefficientShare S * denom) := by
            exact add_le_add (add_le_add (add_le_add hone hboundary) hempty) le_rfl
      _ =
          (oneShare + boundaryPairShare + emptyBoundaryShare +
              (∑ S ∈ sourceClassSupport, coefficientShare S)) * denom := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ 1 * denom :=
        mul_le_mul_of_nonneg_right hshareSum hdenomNonneg
      _ = denom := by
        ring

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorption_of_componentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, ghostShare,
      nonGhostShare, _honeShare, _hboundaryShare, _hemptyShare,
      _hghostShare, _hnonGhostShare, hshareSum, hone, hboundary, hempty,
      hghost, hnonGhost⟩
  refine ⟨ghostShare * denom, nonGhostShare * denom, ?_, ?_, ?_⟩
  · exact hghost
  · exact hnonGhost
  · have hdenomNonneg : 0 ≤ denom := by
      dsimp [denom]
      exact finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
    calc
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
            (ghostShare * denom + nonGhostShare * denom)
          ≤
            oneShare * denom + boundaryPairShare * denom +
              emptyBoundaryShare * denom +
              (ghostShare * denom + nonGhostShare * denom) := by
            exact add_le_add (add_le_add (add_le_add hone hboundary) hempty) le_rfl
      _ =
          (oneShare + boundaryPairShare + emptyBoundaryShare +
              (ghostShare + nonGhostShare)) * denom := by
        ring
      _ ≤ 1 * denom :=
        mul_le_mul_of_nonneg_right hshareSum hdenomNonneg
      _ = denom := by
        ring

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportGhostMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨ghostBudget, nonGhostBudget, hghost, hnonGhost, htotal⟩
  have hcoeff :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        ghostBudget + nonGhostBudget := by
    refine
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_filter_le_filter_not_le
        β H n Ωnz v (fun S => none ∈ S)
        (A := ghostBudget) (B := nonGhostBudget)
        (C := ghostBudget + nonGhostBudget) ?_ ?_ ?_
    · simpa [sourceClassSupport] using hghost
    · simpa [sourceClassSupport] using hnonGhost
    · exact le_rfl
  let base :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htotal' : base + (ghostBudget + nonGhostBudget) ≤ denom := by
    simpa [base, cap, sourceClassSupport, denom, Ωnz] using htotal
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v =
        base +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
      ring
    _ ≤ base + (ghostBudget + nonGhostBudget) :=
      add_le_add le_rfl hcoeff
    _ ≤ denom := htotal'

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportGhostMembershipComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportGhostMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorption_of_componentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportCardinalityComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportCardinalityComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨coefficientBudget, hcase, htotal⟩
  have hcase' :
      ∀ c,
        (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ωnz v).filter
              (fun S => finiteBoundaryGhostSourceClassCardinalityCase S = c),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v S) ≤
          coefficientBudget c := by
    intro c
    simpa [sourceClassSupport] using hcase c
  have hcoeff :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        ∑ c, coefficientBudget c :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_label_sum_le
      β H n Ωnz v
      (fun S => finiteBoundaryGhostSourceClassCardinalityCase S)
      hcase' le_rfl
  let base :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htotal' : base + (∑ c, coefficientBudget c) ≤ denom := by
    simpa [base, cap, sourceClassSupport, denom, Ωnz] using htotal
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v =
        base +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
      ring
    _ ≤ base + ∑ c, coefficientBudget c :=
      add_le_add le_rfl hcoeff
    _ ≤ denom := htotal'

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorption_of_liveEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with ⟨liveBudget, hlive, htotal⟩
  let coefficientBudget : SourceClassEndpointMembershipCase → ℝ :=
    fun c =>
      if finiteBoundaryGhostSourceClassEndpointMembershipLiveCase c then
        liveBudget c
      else
        0
  refine ⟨coefficientBudget, ?_, ?_⟩
  · intro c
    by_cases hc :
        finiteBoundaryGhostSourceClassEndpointMembershipLiveCase c
    · simpa [coefficientBudget, hc, sourceClassSupport] using hlive c hc
    · have hzero :
          (∑ S ∈
            (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
              n Ωnz v).filter
              (fun S =>
                finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ωnz v S) = 0 :=
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_not_live_sum_eq_zero
          β H n Ωnz v hv c hc
      calc
        (∑ S ∈ sourceClassSupport.filter
            (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v S) ≤ 0 := by
            simpa [sourceClassSupport] using le_of_eq hzero
        _ = coefficientBudget c := by
            simp [coefficientBudget, hc]
  · have hbudgetSum :
        (∑ c, coefficientBudget c) =
          ∑ c ∈
            (Finset.univ : Finset SourceClassEndpointMembershipCase).filter
              finiteBoundaryGhostSourceClassEndpointMembershipLiveCase,
            liveBudget c := by
      simp [coefficientBudget, Finset.sum_filter]
    simpa [cap, sourceClassSupport, denom, Ωnz, hbudgetSum] using htotal

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorption_of_explicitLiveEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with ⟨coefficientBudget, hcase, htotal⟩
  refine ⟨coefficientBudget, ?_, ?_⟩
  · intro c hc
    exact hcase c
      ((finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_mem_iff
        c).mpr hc)
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_eq_filter]
      using htotal

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨coefficientBudget, hcase, htotal⟩
  have hcase' :
      ∀ c,
        (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ωnz v).filter
              (fun S =>
                finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v S) ≤
          coefficientBudget c := by
    intro c
    simpa [sourceClassSupport] using hcase c
  have hcoeff :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        ∑ c, coefficientBudget c :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_label_sum_le
      β H n Ωnz v
      (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S)
      hcase' le_rfl
  let base :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htotal' : base + (∑ c, coefficientBudget c) ≤ denom := by
    simpa [base, cap, sourceClassSupport, denom, Ωnz] using htotal
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v =
        base +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
      ring
    _ ≤ base + ∑ c, coefficientBudget c :=
      add_le_add le_rfl hcoeff
    _ ≤ denom := htotal'

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportLiveEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportEndpointMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorption_of_liveEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportLiveEndpointMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorption_of_explicitLiveEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorption_of_budget15
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualBudget15ComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption_of_residualBudget15
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualBudget15ComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption_of_dependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_dependentCoefficientLabelComponentSum
    h

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let denom :=
    finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨coefficientBudget, hcase, htotal⟩
  have hcoeff :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        ∑ S ∈ sourceClassSupport, coefficientBudget S := by
    calc
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v =
        ∑ S ∈ sourceClassSupport,
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v S := by
        simpa [sourceClassSupport] using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_sum
            β H n Ωnz v
      _ ≤ ∑ S ∈ sourceClassSupport, coefficientBudget S :=
        Finset.sum_le_sum (fun S hS => hcase S hS)
  let base :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  have htotal' :
      base + (∑ S ∈ sourceClassSupport, coefficientBudget S) ≤ denom := by
    simpa [base, cap, sourceClassSupport, denom, Ωnz] using htotal
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v =
        base +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
      ring
    _ ≤ base + ∑ S ∈ sourceClassSupport, coefficientBudget S :=
      add_le_add le_rfl hcoeff
    _ ≤ denom := htotal'

end Exact3D
end StatMech
