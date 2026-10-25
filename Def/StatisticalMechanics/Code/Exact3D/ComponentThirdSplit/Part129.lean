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
import Inductive.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part3
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

def unpaidRemainderReservoirSplitBranchPredicate
    (branch : UnpaidRemainderReservoirSplitBranch)
    (R mainGapSum emptyGap : ℝ) : Prop :=
  match branch with
  | UnpaidRemainderReservoirSplitBranch.nonpositive => R ≤ 0
  | UnpaidRemainderReservoirSplitBranch.mainGap => R ≤ mainGapSum
  | UnpaidRemainderReservoirSplitBranch.emptyGap => R ≤ emptyGap
  | UnpaidRemainderReservoirSplitBranch.mixedGap => R ≤ mainGapSum + emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical :
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
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            ∃ branch : UnpaidRemainderReservoirSplitBranch,
              unpaidRemainderReservoirSplitBranchPredicate
                branch R mainGapSum emptyGap

set_option linter.style.longLine false in

def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical :
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
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            R ≤ 0 ∨
              R ≤ mainGapSum ∨
                R ≤ emptyGap ∨
                  R ≤ mainGapSum + emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical :
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
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  R ≤ mainGapSum + emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical :
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
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            let mixedDeficit := R - (mainGapSum + emptyGap)
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  mixedDeficit ≤ 0

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical :
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
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  D ≤ paid + mainGapSum + emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical :
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
            let boundaryMultiplicity :=
              ∑ d ∈ I.image,
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) *
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let mainBudget := (I.image.card : ℝ) * mainTerm
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap := emptyBudget - restoredCopy
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  D + (boundaryMultiplicity + restoredCopy) ≤
                    paid + (mainBudget + emptyBudget)

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical :
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
            let boundaryMultiplicity :=
              ∑ d ∈ I.image,
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) *
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let mainBudget := (I.image.card : ℝ) * mainTerm
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap := emptyBudget - restoredCopy
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ k : ℕ,
                    ∃ demand mainCharge emptyCharge : Fin k → ℝ,
                      (∀ a : Fin k, 0 ≤ demand a) ∧
                        (∀ a : Fin k, 0 ≤ mainCharge a) ∧
                          (∀ a : Fin k, 0 ≤ emptyCharge a) ∧
                            R ≤ ∑ a : Fin k, demand a ∧
                              (∀ a : Fin k,
                                demand a ≤ mainCharge a + emptyCharge a) ∧
                                (∑ a : Fin k, mainCharge a) +
                                    boundaryMultiplicity ≤
                                  mainBudget ∧
                                  (∑ a : Fin k, emptyCharge a) +
                                      restoredCopy ≤
                                    emptyBudget

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical :
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
            let boundaryMultiplicity :=
              ∑ d ∈ I.image,
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) *
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let mainBudget := (I.image.card : ℝ) * mainTerm
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap := emptyBudget - restoredCopy
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ k mainSlots emptySlots : ℕ,
                    ∃ demand : Fin k → ℝ,
                      ∃ mainCap : Fin mainSlots → ℝ,
                        ∃ emptyCap : Fin emptySlots → ℝ,
                          ∃ route :
                              Fin k → Sum (Fin mainSlots) (Fin emptySlots),
                            (∀ a : Fin k, 0 ≤ demand a) ∧
                              (∀ i : Fin mainSlots, 0 ≤ mainCap i) ∧
                                (∀ j : Fin emptySlots, 0 ≤ emptyCap j) ∧
                                  R ≤ ∑ a : Fin k, demand a ∧
                                    Function.Injective route ∧
                                      (∀ a : Fin k,
                                        demand a ≤
                                          match route a with
                                          | Sum.inl i => mainCap i
                                          | Sum.inr j => emptyCap j) ∧
                                        (∑ i : Fin mainSlots, mainCap i) +
                                            boundaryMultiplicity ≤
                                          mainBudget ∧
                                          (∑ j : Fin emptySlots, emptyCap j) +
                                              restoredCopy ≤
                                            emptyBudget

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical :
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
            let boundaryMultiplicity :=
              ∑ d ∈ I.image,
                (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                  ℕ) : ℝ) *
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let mainBudget := (I.image.card : ℝ) * mainTerm
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap := emptyBudget - restoredCopy
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type, ∃ MainSlot : Type, ∃ EmptySlot : Type,
                    ∃ atoms : Finset Atom,
                      ∃ mainSlots : Finset MainSlot,
                        ∃ emptySlots : Finset EmptySlot,
                          ∃ demand : Atom → ℝ,
                            ∃ mainCap : MainSlot → ℝ,
                              ∃ emptyCap : EmptySlot → ℝ,
                                ∃ route : Atom → Sum MainSlot EmptySlot,
                                  (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                                    (∀ i, i ∈ mainSlots → 0 ≤ mainCap i) ∧
                                      (∀ j, j ∈ emptySlots →
                                        0 ≤ emptyCap j) ∧
                                        R ≤ ∑ a ∈ atoms, demand a ∧
                                          (∀ a, a ∈ atoms →
                                            match route a with
                                            | Sum.inl i => i ∈ mainSlots
                                            | Sum.inr j => j ∈ emptySlots) ∧
                                            Set.InjOn route atoms ∧
                                              (∀ a, a ∈ atoms →
                                                demand a ≤
                                                  match route a with
                                                  | Sum.inl i => mainCap i
                                                  | Sum.inr j => emptyCap j) ∧
                                                (∑ i ∈ mainSlots, mainCap i) +
                                                    boundaryMultiplicity ≤
                                                  mainBudget ∧
                                                  (∑ j ∈ emptySlots,
                                                      emptyCap j) +
                                                      restoredCopy ≤
                                                    emptyBudget

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical :
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
                        ∃ route :
                            Atom →
                              Sum
                                (finiteBoundaryGhostCollapsedTwoPointSourceData
                                  n v)
                                Unit,
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

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical :
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
                        ∃ route :
                            {a // a ∈ atoms} →
                              Sum
                                (finiteBoundaryGhostCollapsedTwoPointSourceData
                                  n v)
                                Unit,
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

set_option linter.style.longLine false in


noncomputable def canonicalCapacityCandidateSlots
    {Atom MainSlot : Type*}
    (mainSlots : Finset MainSlot)
    (mainCap : MainSlot → ℝ)
    (emptyCap : ℝ)
    (demand : Atom → ℝ)
    (a : Atom) :
    Finset (Sum MainSlot Unit) := by
  classical
  exact
    ((mainSlots.filter (fun d => demand a ≤ mainCap d)).image
        (Sum.inl : MainSlot → Sum MainSlot Unit)) ∪
      (((Finset.univ : Finset Unit).filter
          (fun _ => demand a ≤ emptyCap)).image
        (Sum.inr : Unit → Sum MainSlot Unit))

end Exact3D
end StatMech
