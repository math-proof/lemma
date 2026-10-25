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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part122
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def unpaidRemainderReservoirSplitBranchFirstTrueSelector :
    UnpaidRemainderReservoirSplitBranchSelector :=
  fun {n} β H Ω v =>
    let cap := boundaryCrossingCap n Ω
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
    let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v
    let mainGapSum :=
      ∑ d ∈ I.image,
        (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v -
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) : ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d))
    let emptyGap :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v -
        (∑ d ∈ I.image,
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
    unpaidRemainderReservoirSplitBranchFirstTrue R mainGapSum emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical :
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
            ∃ mainR emptyR : ℝ,
              R ≤ mainR + emptyR ∧
                mainR +
                    (∑ d ∈ I.image,
                      (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                        ℕ) : ℝ) *
                        finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                          β H d)) ≤
                  (I.image.card : ℝ) *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                      β H n v ∧
                emptyR +
                    (∑ d ∈ I.image,
                      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                        β H d) ≤
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical :
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
            R +
                (∑ d ∈ I.image,
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)) ≤
              (I.image.card : ℝ) *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                  β H n v ∧
            (∑ d ∈ I.image,
              finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical :
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
            (∑ d ∈ I.image,
              (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                ℕ) : ℝ) *
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
              (I.image.card : ℝ) *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                  β H n v ∧
            R +
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                    β H d) ≤
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v

end Exact3D
end StatMech
