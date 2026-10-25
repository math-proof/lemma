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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part130
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical) :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical := by
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
                Nonempty
                  ({b // b ∈ atoms ∧ demand a ≤ demand b} ↪
                    {slot : Slot //
                      slot ∈
                        canonicalCapacityCandidateSlots
                          I.image mainGap emptyGap demand a}))
  intro hnonpos hmainShortcut hemptyShortcut
  rcases hn H hH Ω v hv hnonpos hmainShortcut hemptyShortcut with
    ⟨Atom, atoms, demand, hdemandNonneg, hRle, hThreshold⟩
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  intro a ha
  exact
    canonicalCapacityThresholdCandidateEmbedding_of_thresholdCandidateCard
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand) (a := a)
      (by
        simpa [I, mainGap, emptyGap] using hThreshold a ha)

set_option linter.style.longLine false in


theorem residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
    (h :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical) :
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
    ⟨Atom, atoms, demand, route, hdemandNonneg, hRle, hrouteMem, hinj,
      hrouteCap⟩
  refine ⟨Atom, atoms, demand, hdemandNonneg, hRle, ?_⟩
  exact
    canonicalCapacityThresholdScalarCount_of_globalRouteInjOn
      (atoms := atoms) (mainSlots := I.image) (mainCap := mainGap)
      (emptyCap := emptyGap) (demand := demand) (route := route)
      (hroute := by
        intro b hb
        have hmem := hrouteMem b hb
        have hcap := hrouteCap b hb
        cases hslot : route b with
        | inl d =>
            have hmem' : d ∈ I.image := by
              simpa [hslot] using hmem
            have hcap' : demand b ≤ mainGap d := by
              simpa [hslot] using hcap
            exact ⟨hmem', hcap'⟩
        | inr u =>
            simpa [hslot] using hcap)
      (hinj := hinj)

end Exact3D
end StatMech
