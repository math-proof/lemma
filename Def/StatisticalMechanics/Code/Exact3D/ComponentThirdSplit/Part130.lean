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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part120
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        ∃ candidateSlots :
                            Atom → Finset Slot,
                          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                            R ≤ ∑ a ∈ atoms, demand a ∧
                              (∀ S : Finset Atom, S ⊆ atoms →
                                S.card ≤
                                  (@Finset.biUnion Atom Slot
                                    (Classical.decEq Slot)
                                    S candidateSlots).card) ∧
                                (∀ a, a ∈ atoms →
                                  ∀ slot, slot ∈ candidateSlots a →
                                    match slot with
                                    | Sum.inl d =>
                                        d ∈ I.image ∧ demand a ≤ mainGap d
                                    | Sum.inr _ =>
                                        demand a ≤ emptyGap)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        let candidateSlots : Atom → Finset Slot :=
                          canonicalCapacityCandidateSlots
                            I.image mainGap emptyGap demand
                        (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                          R ≤ ∑ a ∈ atoms, demand a ∧
                            (∀ S : Finset Atom, S ⊆ atoms →
                              S.card ≤
                                (@Finset.biUnion Atom Slot
                                  (Classical.decEq Slot)
                                  S candidateSlots).card)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        let candidateSlots : Atom → Finset Slot :=
                          canonicalCapacityCandidateSlots
                            I.image mainGap emptyGap demand
                        (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                          R ≤ ∑ a ∈ atoms, demand a ∧
                            (∀ a, a ∈ atoms →
                              (atoms.filter
                                (fun b => demand a ≤ demand b)).card ≤
                                  (candidateSlots a).card)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                          R ≤ ∑ a ∈ atoms, demand a ∧
                            (∀ a, a ∈ atoms →
                              (atoms.filter
                                (fun b => demand a ≤ demand b)).card ≤
                                  (I.image.filter
                                    (fun d => demand a ≤ mainGap d)).card +
                                    if demand a ≤ emptyGap then 1 else 0)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        ∃ slotAt : Fin atoms.card → Slot,
                          (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                            R ≤ ∑ a ∈ atoms, demand a ∧
                              (∀ i,
                                match slotAt i with
                                | Sum.inl d => d ∈ I.image
                                | Sum.inr _ => True) ∧
                                Function.Injective slotAt ∧
                                  (∀ a, a ∈ atoms →
                                    ∀ i : Fin atoms.card,
                                      (i : ℕ) <
                                          (atoms.filter
                                            (fun b => demand a ≤ demand b)).card →
                                        match slotAt i with
                                        | Sum.inl d => demand a ≤ mainGap d
                                        | Sum.inr _ => demand a ≤ emptyGap)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        ∃ atomAt : Fin atoms.card → Atom,
                          ∃ slotAt : Fin atoms.card → Slot,
                            (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                              R ≤ ∑ a ∈ atoms, demand a ∧
                                (∀ i, atomAt i ∈ atoms) ∧
                                  Function.Injective atomAt ∧
                                    (∀ a, a ∈ atoms → ∃ i, atomAt i = a) ∧
                                      (∀ i j : Fin atoms.card,
                                        (i : ℕ) ≤ (j : ℕ) →
                                          demand (atomAt j) ≤
                                            demand (atomAt i)) ∧
                                        (∀ i,
                                          match slotAt i with
                                          | Sum.inl d => d ∈ I.image
                                          | Sum.inr _ => True) ∧
                                          Function.Injective slotAt ∧
                                            (∀ i,
                                              match slotAt i with
                                              | Sum.inl d =>
                                                  demand (atomAt i) ≤
                                                    mainGap d
                                              | Sum.inr _ =>
                                                  demand (atomAt i) ≤
                                                    emptyGap)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                          R ≤ ∑ a ∈ atoms, demand a ∧
                            (∀ a, a ∈ atoms →
                              ∃ route : Atom → Slot,
                                (∀ b, b ∈ atoms → demand a ≤ demand b →
                                  match route b with
                                  | Sum.inl d =>
                                      d ∈ I.image ∧ demand a ≤ mainGap d
                                  | Sum.inr _ =>
                                      demand a ≤ emptyGap) ∧
                                  Set.InjOn route
                                    (atoms.filter
                                      (fun b => demand a ≤ demand b) :
                                        Set Atom))

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                          R ≤ ∑ a ∈ atoms, demand a ∧
                            (∀ a, a ∈ atoms →
                              ∃ route :
                                {b // b ∈ atoms ∧ demand a ≤ demand b} →
                                  Slot,
                                (∀ b,
                                  match route b with
                                  | Sum.inl d =>
                                      d ∈ I.image ∧ demand a ≤ mainGap d
                                  | Sum.inr _ =>
                                      demand a ≤ emptyGap) ∧
                                  Function.Injective route)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
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

end Exact3D
end StatMech
